Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.epath.
Require Import GraphLib.reachable.Zweight.
Require Import GraphLib.subgraph.subgraph.
From GraphLib.undirected Require Import tree.
From GraphLib.examples Require Import prim.
From ListLib Require Import Base.Positional General.Length.
From SumLib Require Import ZRange.
From MaxMinLib Require Import MaxMin Interface.
From MonadLib.StateRelMonad Require Export StateRelBasic.
From MonadLib.StateRelMonad Require Import StateRelHoare FixpointLib safeexec_lib.
Require Algorithms.Prim.Prim.

Import ListNotations.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.

(** * 具体图模型 *)

Definition V : Type := Z.
Definition E : Type := Z.
Definition DE : Type := Z.

Record G : Type := mkG {
  graph_from : E -> V;
  graph_to : E -> V;
  graph_weight : E -> Z;
  graph_vertices : list V;
  graph_edges : list E;
}.

(** ** C 数组规格使用的列表取值辅助函数 *)


Lemma Znth_replace_Znth_same_local :
  forall (l : list Z) i v,
    0 <= i < Zlength l ->
    Znth i (replace_Znth i v l) 0 = v.
Proof.
  intros l i v Hi.
  unfold Znth.
  apply Znth_replace_Znth_Same.
  exact Hi.
Qed.

Lemma Znth_replace_Znth_diff_local :
  forall (l : list Z) i j v,
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    i <> j ->
    Znth j (replace_Znth i v l) 0 = Znth j l 0.
Proof.
  intros l i j v Hi Hj Hneq.
  unfold Znth.
  apply Znth_replace_Znth_Diff; auto.
Qed.

Lemma nth_replace_nth_diff_local :
  forall (l : list Z) (i j : nat) v d,
    i <> j ->
    nth j (replace_nth i l v) d = nth j l d.
Proof.
  induction l as [| a l IH]; intros i j v d Hneq.
  - destruct i, j; simpl; reflexivity.
  - destruct i as [| i], j as [| j]; simpl in *.
    + contradiction.
    + reflexivity.
    + reflexivity.
    + apply IH; congruence.
Qed.

Lemma Znth_replace_Znth_diff_nonneg_local :
  forall (l : list Z) i j v,
    0 <= i ->
    0 <= j ->
    i <> j ->
    Znth j (replace_Znth i v l) 0 = Znth j l 0.
Proof.
  intros l i j v Hi Hj Hneq.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_diff_local.
  intro Hnat.
  apply Hneq.
  rewrite <- (Z2Nat.id i) by lia.
  rewrite <- (Z2Nat.id j) by lia.
  f_equal.
  exact Hnat.
Qed.

Lemma Zlength_replace_Znth_local :
  forall {A : Type} (l : list A) i (v : A),
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros A l.
  induction l as [| a l IH]; intros i v; simpl; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat i) eqn:Hi; simpl.
  - do 2 rewrite Zlength_cons. lia.
  - do 2 rewrite Zlength_cons.
    specialize (IH (Z.of_nat n) v).
    replace (Z.to_nat (Z.of_nat n)) with n in IH by lia.
    rewrite IH. lia.
Qed.

Lemma Znth_app_l_local :
  forall (l r : list Z) i,
    0 <= i < Zlength l ->
    Znth i (l ++ r) 0 = Znth i l 0.
Proof.
  intros l r i Hi.
  unfold Znth.
  apply app_nth1.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma Znth_app_r_local :
  forall (l r : list Z) i,
    Zlength l <= i ->
    Znth i (l ++ r) 0 = Znth (i - Zlength l) r 0.
Proof.
  intros l r i Hi.
  unfold Znth.
  rewrite app_nth2.
  - replace (Z.to_nat i - length l)%nat
      with (Z.to_nat (i - Zlength l)) by
        (rewrite Zlength_correct in *; lia).
    reflexivity.
  - rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma Znth_app_two_first_new_local :
  forall (l : list Z) a b,
    Znth (Zlength l) ((l ++ [a]) ++ [b]) 0 = a.
Proof.
  intros l a b.
  rewrite Znth_app_l_local.
  - rewrite Znth_app_r_local by lia.
    replace (Zlength l - Zlength l) with 0 by lia.
    unfold Znth; simpl.
    reflexivity.
  - pose proof (Zlength_app l (a :: nil)) as Hlen.
    rewrite Zlength_cons, Zlength_nil in Hlen.
    pose proof (Zlength_nonneg l).
    lia.
Qed.

Lemma Znth_app_two_second_new_local :
  forall (l : list Z) a b,
    Znth (Zlength l + 1) ((l ++ [a]) ++ [b]) 0 = b.
Proof.
  intros l a b.
  rewrite Znth_app_r_local.
  - replace (Zlength l + 1 - Zlength (l ++ [a])) with 0 by
      (pose proof (Zlength_app l (a :: nil)) as Hlen;
       rewrite Zlength_cons, Zlength_nil in Hlen; lia).
    unfold Znth; simpl.
    reflexivity.
  - pose proof (Zlength_app l (a :: nil)) as Hlen.
    rewrite Zlength_cons, Zlength_nil in Hlen.
    rewrite Zlength_correct in *.
    lia.
Qed.

(** ** 图的基本操作和良构条件 *)

Definition edge_src (g : G) (e : E) : V :=
  graph_from g e.

Definition edge_dst (g : G) (e : E) : V :=
  graph_to g e.

Definition graph_edge_count (g : G) : Z :=
  Zlength (graph_edges g).

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

Definition edge_endpoints_valid (g : G) (e : E) : Prop :=
  In (edge_src g e) (graph_vertices g) /\
  In (edge_dst g e) (graph_vertices g).

Definition edge_valid (g : G) (e : E) : Prop :=
  In e (graph_edges g).

Definition graph_step (g : G) (e : E) (u v : V) : Prop :=
  edge_valid g e /\
  edge_endpoints_valid g e /\
  ((u = edge_src g e /\ v = edge_dst g e) \/
   (u = edge_dst g e /\ v = edge_src g e)).

Definition graph_step_wf (g : G) : Prop :=
  forall e, edge_valid g e -> exists u v, graph_step g e u v.

Definition graph_wf : G -> Prop := graph_step_wf.

(** * GraphLib 图接口实例 *)

#[export] Instance graph_instance : Graph G V E := {|
  vvalid := fun g v => In v (graph_vertices g);
  evalid := edge_valid;
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
  intros g e x1 y1 x2 y2 Hg H1 H2.
  destruct H1 as [_ [_ Hxy1]].
  destruct H2 as [_ [_ Hxy2]].
  destruct Hxy1 as [[-> ->] | [-> ->]];
    destruct Hxy2 as [[-> ->] | [-> ->]]; auto.
Qed.

#[export] Instance finite_instance : FiniteGraph G V E.
Proof.
  refine {| listV := graph_vertices |}.
  intros g Hg v Hv; exact Hv.
Qed.

Definition valid_edges (g : G) : list E :=
  nodup Z.eq_dec (graph_edges g).

#[export] Instance elist_bijective_instance : EListBijective G V E.
Proof.
  refine {| bijective_listE := valid_edges |}.
  - intros g Hg.
    unfold valid_edges.
    apply NoDup_nodup.
  - intros g Hg e.
    unfold valid_edges, edge_valid.
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

(** * Prim 相关接口和包装 *)

Definition St : Type := @Prim.St G.

Definition empty_graph_of (g : G) (src : V) : G :=
  mkG (graph_from g) (graph_to g) (graph_weight g) (src :: nil) nil.

Lemma empty_graph_valid_of : forall g src, gvalid (empty_graph_of g src).
Proof.
  intros g src.
  unfold gvalid, gvalid_instance, graph_wf.
  intros e He.
  contradiction.
Qed.

#[export] Instance emptyGraph_instance (g : G) (src : V) :
  Prim.emptyGraph G V E src.
Proof.
  refine {| Prim.empty_graph := empty_graph_of g src |}.
  - apply empty_graph_valid_of.
  - intros v. simpl. split.
    + intros [Hv | []]; auto.
    + intros ->; auto.
  - intros e. simpl. unfold edge_valid. split; intros H.
    + destruct H.
    + contradiction.
Defined.

Definition initSt (g : G) (src : V) : St :=
  @Prim.initSt G V E graph_instance gvalid_instance src
    (emptyGraph_instance g src).

Definition initStPred (g : G) (src : V) : St -> Prop :=
  fun s => s = initSt g src.

Definition state_vertex_count (s : St) : Z :=
  vertex_num s.(Prim.graph_in_state).

Lemma initSt_vvalid :
  forall g src v,
    vvalid (Prim.graph_in_state (initSt g src)) v <-> v = src.
Proof.
  intros g src v.
  unfold initSt.
  simpl.
  unfold empty_graph_of, vvalid, graph_instance.
  simpl.
  split.
  - intros [H | []]; symmetry; exact H.
  - intros ->; left; reflexivity.
Qed.

Lemma initSt_state_vertex_count :
  forall g src,
    state_vertex_count (initSt g src) = 1.
Proof.
  intros g src.
  unfold state_vertex_count, vertex_num.
  assert (Hg : gvalid (Prim.graph_in_state (initSt g src))).
  {
    unfold initSt.
    simpl.
    apply empty_graph_valid_of.
  }
  assert (Hperm :
    Permutation
      (bijective_listV (Prim.graph_in_state (initSt g src)))
      [src]).
  {
    apply NoDup_Permutation.
    - apply bijective_listV_NoDup; exact Hg.
    - constructor; [intro H; inversion H | constructor].
    - intros v.
      rewrite bijective_vertices by exact Hg.
      rewrite initSt_vvalid.
      simpl.
      split.
      + intros ->; auto.
      + intros [Hv | []]; symmetry; exact Hv.
  }
  apply Permutation_length in Hperm.
  rewrite !Zlength_correct.
  rewrite Hperm.
  reflexivity.
Qed.

Definition Prim2 (g : G) : program St unit :=
  @range_iter St unit
    0
    (Zlength (bijective_listV g) - 1)
    (fun _ _ =>
       @Prim.Prim_body G V E graph_instance g edge_weight_instance)
    tt.


Definition Prim2_loop (g : G) (i : Z) : program St unit :=
  @range_iter St unit
    i
    (Zlength (bijective_listV g) - 1)
    (fun _ _ =>
       @Prim.Prim_body G V E graph_instance g edge_weight_instance)
    tt.

Definition prim_state_is (s0 : St) : St -> Prop :=
  fun s => s = s0.

Definition prim_state_graph_matches (g:G) : St -> Prop :=
  fun s => s.(Prim.graph_in_state) = g.


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
  unfold evalid, graph_instance, edge_valid, add_edge_graph; simpl.
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
  unfold step_aux, graph_instance, graph_step.
  rewrite add_edge_graph_evalid by auto.
  unfold edge_src, edge_dst, add_edge_graph; simpl.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros [_ [_ Hxy]].
      right; split; [reflexivity|].
      destruct Hxy as [[-> ->] | [-> ->]]; auto.
    + intros [Hold | [_ Hxy]].
      * exfalso; apply Hne; exact (proj1 Hold).
      * split; [right; reflexivity|].
        split.
        -- unfold edge_endpoints_valid, edge_src, edge_dst, add_edge_graph; simpl.
           destruct (Z.eq_dec e e) as [_ | Hneq]; [|contradiction].
           split; simpl; auto.
        -- exact Hxy.
  - split.
    + intros [[Hold | Heq] [_ Hxy]]; [|contradiction].
      destruct (Hg a Hold) as [p [q Hstep_old]].
      destruct Hstep_old as [_ [Hends _]].
      left; split; [exact Hold|split; auto].
    + intros [Hold | [Heq Hxy]]; [|contradiction].
      destruct Hold as [Hea [Hends Hxy]].
      split; [left; exact Hea|].
      split.
      * unfold edge_endpoints_valid, edge_src, edge_dst, add_edge_graph in *; simpl in *.
        destruct (Z.eq_dec a e) as [Heq | _]; [contradiction|].
        destruct Hends as [Hsrc Hdst]; split; simpl; auto.
      * exact Hxy.
Qed.

Lemma add_edge_graph_evalid_any :
  forall g u v e a,
    evalid (add_edge_graph g u v e) a <-> evalid g a \/ a = e.
Proof.
  intros g u v e a.
  unfold evalid, graph_instance, edge_valid, add_edge_graph; simpl.
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
  unfold step_aux, graph_instance, graph_step.
  rewrite add_edge_graph_evalid_any.
  unfold edge_src, edge_dst, add_edge_graph; simpl.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros [_ [_ Hxy]].
      right; split; [reflexivity|].
      destruct Hxy as [[-> ->] | [-> ->]]; auto.
    + intros [Hold | [_ Hxy]].
      * exfalso; apply Hne; exact (proj1 Hold).
      * split; [right; reflexivity|].
        split.
        -- unfold edge_endpoints_valid, edge_src, edge_dst, add_edge_graph; simpl.
           destruct (Z.eq_dec e e) as [_ | Hneq]; [|contradiction].
           split; simpl; auto.
        -- exact Hxy.
  - split.
    + intros [[Hold | Heq] [_ Hxy]]; [|contradiction].
      destruct (Hg a Hold) as [p [q Hstep_old]].
      destruct Hstep_old as [_ [Hends _]].
      left; split; [exact Hold|split; auto].
    + intros [Hold | [Heq Hxy]]; [|contradiction].
      destruct Hold as [Hea [Hends Hxy]].
      split; [left; exact Hea|].
      split.
      * unfold edge_endpoints_valid, edge_src, edge_dst, add_edge_graph in *; simpl in *.
        destruct (Z.eq_dec a e) as [Heq | _]; [contradiction|].
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
  unfold gvalid, gvalid_instance, graph_wf, graph_step_wf in *.
  intros a Ha.
  unfold edge_valid, add_edge_graph in Ha; simpl in Ha.
  destruct Ha as [Ha_new | Ha_old].
  - subst a.
    exists u, v.
    unfold graph_step, edge_valid, edge_endpoints_valid, edge_src, edge_dst,
      add_edge_graph, graph_instance.
    simpl.
    destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
    split; [left; reflexivity |].
    split; [split; simpl; auto | left; split; reflexivity].
  - destruct (Z.eq_dec a e) as [Ha_eq | Ha_neq].
    + subst a.
      exists u, v.
      unfold graph_step, edge_valid, edge_endpoints_valid, edge_src, edge_dst,
        add_edge_graph, graph_instance.
      simpl.
      destruct (Z.eq_dec e e) as [_ | Hneq]; [| contradiction].
      split; [left; reflexivity |].
      split; [split; simpl; auto | left; split; reflexivity].
    + specialize (Hg a Ha_old) as [x [y Hstep]].
      exists x, y.
      destruct Hstep as [_ [Hends Hxy]].
      unfold graph_step, edge_valid, edge_endpoints_valid, edge_src, edge_dst,
        add_edge_graph, graph_instance in *.
      simpl in *.
      destruct (Z.eq_dec a e) as [Ha_eq' | _]; [contradiction |].
      split; [right; exact Ha_old |].
      destruct Hends as [Hsrc Hdst].
      split; [split; simpl; auto | exact Hxy].
Qed.

Lemma add_edge_graph_vertex_num_new_vertex :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    ~ vvalid g v ->
    vertex_num (add_edge_graph g u v e) = vertex_num g + 1.
Proof.
  intros g u v e Hg Hu Hvout.
  pose proof (add_edge_graph_gvalid_new_vertex g u v e Hg Hu Hvout) as Hgadd.
  assert (Hperm :
    Permutation
      (bijective_listV (add_edge_graph g u v e))
      (v :: bijective_listV g)).
  {
    apply NoDup_Permutation.
    - apply bijective_listV_NoDup; exact Hgadd.
    - constructor.
      + rewrite bijective_vertices by exact Hg.
        exact Hvout.
      + apply bijective_listV_NoDup; exact Hg.
    - intros x.
      rewrite bijective_vertices by exact Hgadd.
      rewrite add_edge_graph_vvalid.
      simpl.
      rewrite bijective_vertices by exact Hg.
      split.
      + intros [Hx | [Hx | Hx]].
        * right; exact Hx.
        * subst x; right; exact Hu.
        * subst x; left; reflexivity.
      + intros [Hx | Hx].
        * subst x; right; right; reflexivity.
        * left; exact Hx.
  }
  unfold vertex_num.
  apply Permutation_length in Hperm.
  rewrite !Zlength_correct.
  rewrite Hperm.
  simpl.
  lia.
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
  unfold evalid, graph_instance, edge_valid, remove_edge_graph; simpl.
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
  unfold step_aux, graph_instance, graph_step.
  rewrite remove_edge_graph_evalid.
  destruct (Z.eq_dec a e) as [Ha | Ha].
  - subst a.
    split.
    + intros Hcur.
      right; split; [reflexivity|].
      change (step_aux g e x y) in Hcur.
      pose proof (step_aux_unique_undirected g e u v x y Hg Hstep Hcur)
        as [[-> ->] | [-> ->]]; auto.
    + intros [[[ _ Hneq] _] | [_ Hxy]]; [contradiction|].
      destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
      change (step_aux g e v u).
      apply step_sym; exact Hstep.
  - split.
    + intros [Hea [Hends Hxy]].
      left; split; [split; auto|].
      split; [exact Hends|exact Hxy].
    + intros [[[Hea _] [Hends Hxy]] | [Heq _]]; [split; auto|contradiction].
Qed.

#[export] Instance addEdgeExist_instance :
  addEdgeExist G V E.
Proof.
  constructor.
  - intros g u v e Hg Hu Hv Hne.
    exists (add_edge_graph g u v e).
    split.
    + intros a Ha.
      rewrite add_edge_graph_evalid in Ha by auto.
      destruct Ha as [Ha | ->].
      * destruct (Hg a Ha) as [x [y Hstep]].
        exists x, y.
        rewrite add_edge_graph_step by auto.
        left; exact Hstep.
      * exists u, v.
        rewrite add_edge_graph_step by auto.
        right; split; [reflexivity|auto].
    + constructor.
      * intros x. apply add_edge_graph_vvalid.
      * intros a. apply add_edge_graph_evalid; auto.
      * intros x y a. apply add_edge_graph_step; auto.
  - intros g u v e Hg Hu Hv He Hstep.
    exists (remove_edge_graph g e).
    split.
    + intros a Ha.
      rewrite remove_edge_graph_evalid in Ha.
      destruct Ha as [Ha Hneq].
      destruct (Hg a Ha) as [x [y Hstep_a]].
      destruct (proj1 (remove_edge_graph_step g u v e x y a Hg Hstep) Hstep_a)
        as [Hremove | [Heq _]].
      * exists x, y; exact Hremove.
      * contradiction.
    + split.
      * constructor.
        -- intros x. rewrite remove_edge_graph_vvalid.
           split.
           ++ intros Hx; left; exact Hx.
           ++ intros [Hx | [Hx | Hx]].
              ** exact Hx.
              ** subst; exact Hu.
              ** subst; exact Hv.
        -- intros a. rewrite remove_edge_graph_evalid. split.
           ++ intros Ha; destruct (Z.eq_dec a e) as [-> | Hneq]; auto.
           ++ intros [[Ha _] | ->]; [exact Ha | exact He].
        -- intros x y a. apply remove_edge_graph_step; auto.
      * repeat split.
        -- rewrite remove_edge_graph_vvalid; exact Hu.
        -- rewrite remove_edge_graph_vvalid; exact Hv.
        -- rewrite remove_edge_graph_evalid. intros [_ Hneq]; auto.
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




Record PrimEnv (g : G) (src : V) : Prop := mkPrimEnv {
  prim_graph_valid : gvalid g;
  prim_src_valid : vvalid g src;
  prim_connected : connected g;
}.




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
    Zlength (graph_vertices g) = n.
Proof.
  intros n m from to wt g Hgraph.
  destruct Hgraph as [Hvertices [_ [Hn _]]].
  rewrite Hvertices.
  rewrite Zlength_Zrange by lia.
  lia.
Qed.

Lemma array_graph_vertex_range :
  forall n m from to wt g v,
    array_graph n m from to wt g ->
    In v (graph_vertices g) ->
    0 <= v < n.
Proof.
  intros n m from to wt g v Hgraph Hv.
  unfold array_graph in Hgraph.
  destruct Hgraph as [Hvertices [_ [Hn_nonneg _]]].
  rewrite Hvertices in Hv.
  rewrite <- In_Zrange in Hv.
  exact Hv.
Qed.

Lemma array_graph_vertex_in :
  forall n m from to wt g v,
    array_graph n m from to wt g ->
    0 <= v < n ->
    In v (graph_vertices g).
Proof.
  intros n m from to wt g v Hgraph Hv.
  unfold array_graph in Hgraph.
  destruct Hgraph as [Hvertices [_ [Hn_nonneg _]]].
  rewrite Hvertices.
  rewrite <- In_Zrange.
  exact Hv.
Qed.

Lemma array_graph_gvalid :
  forall n m from to wt g,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    gvalid g.
Proof.
  intros n m from to wt g Hgraph Hfrom_valid Hto_valid.
  unfold gvalid, gvalid_instance, graph_wf, graph_step_wf.
  intros e He.
  unfold array_graph in Hgraph.
  destruct Hgraph as
    [Hvertices [Hedges [_ [_ [_ [_ [_ Hdata]]]]]]].
  unfold evalid, graph_instance, edge_valid in He.
  rewrite Hedges in He.
  pose proof He as Hin_edge.
  rewrite <- In_Zrange in He.
  specialize (Hdata e Hin_edge) as [Hfrom [Hto _]].
  exists (Znth e from 0), (Znth e to 0).
  unfold step_aux, graph_instance, graph_step.
  split.
  - unfold edge_valid. rewrite Hedges. rewrite <- In_Zrange. exact He.
  - split.
    + unfold edge_endpoints_valid, edge_src, edge_dst.
      rewrite Hfrom, Hto, Hvertices.
      split; rewrite <- In_Zrange; [apply Hfrom_valid | apply Hto_valid]; exact He.
    + left; split; [symmetry; exact Hfrom | symmetry; exact Hto].
Qed.

(** * 由原图拆出的有向边数组 *)

Definition directed_array_graph_prefix
    (e_bound : E)
    (g : G)
    (from_new to_new wt_new : list DE) : Prop :=
  0 <= e_bound <= graph_edge_count g /\
  Zlength from_new = 2 * e_bound /\
  Zlength to_new = 2 * e_bound /\
  Zlength wt_new = 2 * e_bound /\
  forall e,
    0 <= e < e_bound ->
    Znth (2 * e) from_new 0 = graph_from g e /\
    Znth (2 * e) to_new 0 = graph_to g e /\
    Znth (2 * e) wt_new 0 = graph_weight g e /\
    Znth (2 * e + 1) from_new 0 = graph_to g e /\
    Znth (2 * e + 1) to_new 0 = graph_from g e /\
    Znth (2 * e + 1) wt_new 0 = graph_weight g e.

Definition directed_array_graph
    (g : G)
    (from_new to_new wt_new : list DE) : Prop :=
  directed_array_graph_prefix (graph_edge_count g) g from_new to_new wt_new.

Lemma directed_array_graph_prefix_0_nil :
  forall g,
    0 <= graph_edge_count g ->
    directed_array_graph_prefix 0 g nil nil nil.
Proof.
  intros g Hcount.
  unfold directed_array_graph_prefix.
  split; [lia |].
  split; [rewrite Zlength_nil; lia |].
  split; [rewrite Zlength_nil; lia |].
  split; [rewrite Zlength_nil; lia |].
  intros e He; lia.
Qed.

Lemma directed_array_graph_prefix_finish :
  forall g from_new to_new wt_new e_bound,
    directed_array_graph_prefix e_bound g from_new to_new wt_new ->
    e_bound >= graph_edge_count g ->
    e_bound <= graph_edge_count g ->
    directed_array_graph g from_new to_new wt_new.
Proof.
  intros g from_new to_new wt_new e_bound Hprefix Hge Hle.
  unfold directed_array_graph.
  replace e_bound with (graph_edge_count g) in Hprefix by lia.
  exact Hprefix.
Qed.

Lemma directed_prefix_even_index_range :
  forall edge bound len,
    len = 2 * bound ->
    0 <= edge < bound ->
    0 <= 2 * edge < len.
Proof.
  intros; lia.
Qed.

Lemma directed_prefix_odd_index_range :
  forall edge bound len,
    len = 2 * bound ->
    0 <= edge < bound ->
    0 <= 2 * edge + 1 < len.
Proof.
  intros; lia.
Qed.

Lemma directed_array_graph_prefix_snoc :
  forall n m from to wt g i from_new to_new wt_new,
    array_graph n m from to wt g ->
    directed_array_graph_prefix i g from_new to_new wt_new ->
    0 <= i < m ->
    directed_array_graph_prefix (i + 1) g
      ((from_new ++ [Znth i from 0]) ++ [Znth i to 0])
      ((to_new ++ [Znth i to 0]) ++ [Znth i from 0])
      ((wt_new ++ [Znth i wt 0]) ++ [Znth i wt 0]).
Proof.
  intros n m from to wt g i from_new to_new wt_new Hgraph Hprefix Hi.
  unfold DE in *.
  unfold E in *.
  unfold directed_array_graph_prefix in *.
  destruct Hprefix as [Hrange [Hlen_from [Hlen_to [Hlen_wt Hdata]]]].
  assert (Hcount: graph_edge_count g = m)
    by (eapply array_graph_edge_count; eauto).
  split.
  { lia. }
  split.
  { repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
    repeat rewrite Zlength_nil; lia. }
  split.
  { repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
    repeat rewrite Zlength_nil; lia. }
  split.
  { repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
    repeat rewrite Zlength_nil; lia. }
  intros edge Hedge.
  destruct Hgraph as [_ [_ [_ [_ [_ [_ [_ Hgraph_data]]]]]]].
  assert (edge < i \/ edge = i) as [He_lt | He_eq] by lia.
  + assert (Hedge_old: 0 <= edge < i) by lia.
    specialize (Hdata edge Hedge_old).
    destruct Hdata as [Hf0 [Ht0 [Hw0 [Hf1 [Ht1 Hw1]]]]].
    assert (Hedge_even_from: 0 <= 2 * edge < Zlength from_new) by
      (eapply directed_prefix_even_index_range; eauto).
    assert (Hedge_even_to: 0 <= 2 * edge < Zlength to_new) by
      (eapply directed_prefix_even_index_range; eauto).
    assert (Hedge_even_wt: 0 <= 2 * edge < Zlength wt_new) by
      (eapply directed_prefix_even_index_range; eauto).
    assert (Hedge_odd_from: 0 <= 2 * edge + 1 < Zlength from_new) by
      (eapply directed_prefix_odd_index_range; eauto).
    assert (Hedge_odd_to: 0 <= 2 * edge + 1 < Zlength to_new) by
      (eapply directed_prefix_odd_index_range; eauto).
    assert (Hedge_odd_wt: 0 <= 2 * edge + 1 < Zlength wt_new) by
      (eapply directed_prefix_odd_index_range; eauto).
    repeat split.
    * rewrite Znth_app_l_local.
      -- rewrite Znth_app_l_local by exact Hedge_even_from.
         exact Hf0.
      -- rewrite Zlength_app, Zlength_cons, Zlength_nil.
         pose proof (Zlength_nonneg from_new). lia.
    * rewrite Znth_app_l_local.
      -- rewrite Znth_app_l_local by exact Hedge_even_to.
         exact Ht0.
      -- rewrite Zlength_app, Zlength_cons, Zlength_nil.
         pose proof (Zlength_nonneg to_new). lia.
    * rewrite Znth_app_l_local.
      -- rewrite Znth_app_l_local by exact Hedge_even_wt.
         exact Hw0.
      -- rewrite Zlength_app, Zlength_cons, Zlength_nil.
         pose proof (Zlength_nonneg wt_new). lia.
    * rewrite Znth_app_l_local.
      -- rewrite Znth_app_l_local by exact Hedge_odd_from.
         exact Hf1.
      -- rewrite Zlength_app, Zlength_cons, Zlength_nil.
         pose proof (Zlength_nonneg from_new). lia.
    * rewrite Znth_app_l_local.
      -- rewrite Znth_app_l_local by exact Hedge_odd_to.
         exact Ht1.
      -- rewrite Zlength_app, Zlength_cons, Zlength_nil.
         pose proof (Zlength_nonneg to_new). lia.
    * rewrite Znth_app_l_local.
      -- rewrite Znth_app_l_local by exact Hedge_odd_wt.
         exact Hw1.
      -- rewrite Zlength_app, Zlength_cons, Zlength_nil.
         pose proof (Zlength_nonneg wt_new). lia.
  + subst edge.
    specialize (Hgraph_data i ltac:(rewrite <- In_Zrange; lia)).
    destruct Hgraph_data as [Hf [Ht Hw]].
    assert (Hlen_from_plus: Zlength from_new + 1 = 2 * i + 1).
    { replace (Zlength from_new) with (2 * i) by (symmetry; exact Hlen_from); lia. }
    assert (Hlen_to_plus: Zlength to_new + 1 = 2 * i + 1).
    { replace (Zlength to_new) with (2 * i) by (symmetry; exact Hlen_to); lia. }
    assert (Hlen_wt_plus: Zlength wt_new + 1 = 2 * i + 1).
    { replace (Zlength wt_new) with (2 * i) by (symmetry; exact Hlen_wt); lia. }
    repeat split.
    * replace (2 * i) with (Zlength from_new) by exact Hlen_from.
      rewrite Znth_app_two_first_new_local.
      symmetry; exact Hf.
    * replace (2 * i) with (Zlength to_new) by exact Hlen_to.
      rewrite Znth_app_two_first_new_local.
      symmetry; exact Ht.
    * replace (2 * i) with (Zlength wt_new) by exact Hlen_wt.
      rewrite Znth_app_two_first_new_local.
      symmetry; exact Hw.
    * replace (2 * i + 1) with (Zlength from_new + 1) by exact Hlen_from_plus.
      rewrite Znth_app_two_second_new_local.
      symmetry; exact Ht.
    * replace (2 * i + 1) with (Zlength to_new + 1) by exact Hlen_to_plus.
      rewrite Znth_app_two_second_new_local.
      symmetry; exact Hf.
    * replace (2 * i + 1) with (Zlength wt_new + 1) by exact Hlen_wt_plus.
      rewrite Znth_app_two_second_new_local.
      symmetry; exact Hw.
Qed.

Lemma array_graph_directed_edge_valid :
  forall n m from to wt g de,
    array_graph n m from to wt g ->
    0 <= de < 2 * m ->
    edge_valid g (de / 2).
Proof.
  intros n m from to wt g de Hgraph Hde.
  destruct Hgraph as [_ [Hedges [_ [_ [_ [_ [_ _]]]]]]].
  unfold edge_valid.
  rewrite Hedges.
  rewrite <- In_Zrange.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma directed_edge_div2_bound :
  forall g de,
    0 <= de < 2 * graph_edge_count g ->
    0 <= de / 2 < graph_edge_count g.
Proof.
  intros g de Hde.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma directed_array_graph_step :
  forall g from_new to_new wt_new de,
    directed_array_graph g from_new to_new wt_new ->
    gvalid g ->
    0 <= de < 2 * graph_edge_count g ->
    edge_valid g (de / 2) ->
    step_aux g (de / 2) (Znth de from_new 0) (Znth de to_new 0).
Proof.
  intros g from_new to_new wt_new de Hdir Hg Hde Hedge.
  unfold directed_array_graph, directed_array_graph_prefix in Hdir.
  destruct Hdir as [_ [_ [_ [_ Hdata]]]].
  pose proof (directed_edge_div2_bound g de Hde) as Hhalf.
  specialize (Hdata (de / 2) Hhalf).
  destruct Hdata as [Hfrom_even [Hto_even [_ [Hfrom_odd [Hto_odd _]]]]].
  pose proof (Hg (de / 2) Hedge) as [u [v Hstep_any]].
  destruct Hstep_any as [_ [Hendpoints _]].
  unfold step_aux, graph_instance, graph_step.
  split; [exact Hedge |].
  split; [exact Hendpoints |].
  pose proof (Z.div_mod de 2 ltac:(lia)) as Hdivmod.
  pose proof (Z.mod_pos_bound de 2 ltac:(lia)) as Hmod_bound.
  assert (de mod 2 = 0 \/ de mod 2 = 1) as [Hmod | Hmod] by lia.
  - left.
    replace de with (2 * (de / 2)) by lia.
    replace (2 * (de / 2) / 2) with (de / 2).
    2: { symmetry. rewrite Z.mul_comm. apply Z.div_mul; lia. }
    split; [exact Hfrom_even | exact Hto_even].
  - right.
    replace de with (2 * (de / 2) + 1) by lia.
    replace ((2 * (de / 2) + 1) / 2) with (de / 2).
    2: {
      symmetry.
      rewrite Z.mul_comm.
      rewrite Z.div_add_l by lia.
      replace (1 / 2) with 0 by reflexivity.
      lia.
    }
    split; [exact Hfrom_odd | exact Hto_odd].
Qed.

Lemma directed_array_graph_weight :
  forall g from_new to_new wt_new de,
    directed_array_graph g from_new to_new wt_new ->
    0 <= de < 2 * graph_edge_count g ->
    weight g (de / 2) = Some (Znth de wt_new 0).
Proof.
  intros g from_new to_new wt_new de Hdir Hde.
  unfold directed_array_graph, directed_array_graph_prefix in Hdir.
  destruct Hdir as [_ [_ [_ [_ Hdata]]]].
  pose proof (directed_edge_div2_bound g de Hde) as Hhalf.
  specialize (Hdata (de / 2) Hhalf).
  destruct Hdata as [_ [_ [Hwt_even [_ [_ Hwt_odd]]]]].
  unfold weight, edge_weight_instance.
  pose proof (Z.div_mod de 2 ltac:(lia)) as Hdivmod.
  pose proof (Z.mod_pos_bound de 2 ltac:(lia)) as Hmod_bound.
  assert (de mod 2 = 0 \/ de mod 2 = 1) as [Hmod | Hmod] by lia.
  - replace de with (2 * (de / 2)) by lia.
    replace (2 * (de / 2) / 2) with (de / 2).
    2: { symmetry. rewrite Z.mul_comm. apply Z.div_mul; lia. }
    rewrite Hwt_even.
    reflexivity.
  - replace de with (2 * (de / 2) + 1) by lia.
    replace ((2 * (de / 2) + 1) / 2) with (de / 2).
    2: {
      symmetry.
      rewrite Z.mul_comm.
      rewrite Z.div_add_l by lia.
      replace (1 / 2) with 0 by reflexivity.
      lia.
    }
    rewrite Hwt_odd.
    reflexivity.
Qed.

Lemma directed_array_graph_weight_range :
  forall n m from to wt g from_new to_new wt_new de,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    (forall e, 0 <= e < m -> 0 <= Znth e wt 0 < 1000000000) ->
    0 <= de < 2 * m ->
    0 <= Znth de wt_new 0 < 1000000000.
Proof.
  intros n m from to wt g from_new to_new wt_new de
         Hgraph Hdir Hwt_range Hde.
  pose proof (array_graph_edge_count _ _ _ _ _ _ Hgraph) as Hcount.
  assert (Hde_count : 0 <= de < 2 * graph_edge_count g) by lia.
  pose proof (directed_edge_div2_bound g de Hde_count) as Hhalf_count.
  assert (Hhalf : 0 <= de / 2 < m) by lia.
  assert (Hgraph_weight : graph_weight g (de / 2) = Znth (de / 2) wt 0).
  {
    unfold array_graph in Hgraph.
    destruct Hgraph as [_ [_ [_ [_ [_ [_ [_ Hedges]]]]]]].
    specialize (Hedges (de / 2)).
    assert (Hin : In (de / 2) (Zrange 0 m)).
    { rewrite <- In_Zrange; exact Hhalf. }
    specialize (Hedges Hin).
    tauto.
  }
  unfold directed_array_graph, directed_array_graph_prefix in Hdir.
  destruct Hdir as [_ [_ [_ [_ Hdata]]]].
  specialize (Hdata (de / 2) Hhalf_count).
  destruct Hdata as [_ [_ [Hwt_even [_ [_ Hwt_odd]]]]].
  pose proof (Z.div_mod de 2 ltac:(lia)) as Hdivmod.
  pose proof (Z.mod_pos_bound de 2 ltac:(lia)) as Hmod_bound.
  assert (de mod 2 = 0 \/ de mod 2 = 1) as [Hmod | Hmod] by lia.
  - replace de with (2 * (de / 2)) by lia.
    rewrite Hwt_even.
    rewrite Hgraph_weight.
    apply Hwt_range; exact Hhalf.
  - replace de with (2 * (de / 2) + 1) by lia.
    rewrite Hwt_odd.
    rewrite Hgraph_weight.
    apply Hwt_range; exact Hhalf.
Qed.

Lemma directed_array_graph_from_range :
  forall n m from to wt g from_new to_new wt_new de,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    0 <= de < 2 * m ->
    0 <= Znth de from_new 0 < n.
Proof.
  intros n m from to wt g from_new to_new wt_new de
         Hgraph Hdir Hfrom_range Hto_range Hde.
  pose proof (array_graph_edge_count _ _ _ _ _ _ Hgraph) as Hcount.
  unfold directed_array_graph, directed_array_graph_prefix in Hdir.
  destruct Hdir as [_ [_ [_ [_ Hdata]]]].
  assert (Hhalf: 0 <= de / 2 < m).
  {
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  }
  assert (Hhalf_count: 0 <= de / 2 < graph_edge_count g) by lia.
  specialize (Hdata (de / 2) Hhalf_count).
  destruct Hdata as [Hfrom_even [_ [_ [Hfrom_odd [_ _]]]]].
  pose proof (Z.div_mod de 2 ltac:(lia)) as Hdivmod.
  pose proof (Z.mod_pos_bound de 2 ltac:(lia)) as Hmod_bound.
  assert (de mod 2 = 0 \/ de mod 2 = 1) as [Hmod | Hmod] by lia.
  - replace de with (2 * (de / 2)) by lia.
    rewrite Hfrom_even.
    unfold array_graph in Hgraph.
    destruct Hgraph as [_ [_ [_ [_ [_ [_ [_ Hedges]]]]]]].
    specialize (Hedges (de / 2)).
    assert (Hin: In (de / 2) (Zrange 0 m)).
    { rewrite <- In_Zrange; exact Hhalf. }
    specialize (Hedges Hin).
    destruct Hedges as [Hfrom _].
    rewrite Hfrom.
    apply Hfrom_range; exact Hhalf.
  - replace de with (2 * (de / 2) + 1) by lia.
    rewrite Hfrom_odd.
    unfold array_graph in Hgraph.
    destruct Hgraph as [_ [_ [_ [_ [_ [_ [_ Hedges]]]]]]].
    specialize (Hedges (de / 2)).
    assert (Hin: In (de / 2) (Zrange 0 m)).
    { rewrite <- In_Zrange; exact Hhalf. }
    specialize (Hedges Hin).
    destruct Hedges as [_ [Hto _]].
    rewrite Hto.
    apply Hto_range; exact Hhalf.
Qed.

Lemma directed_array_graph_to_range :
  forall n m from to wt g from_new to_new wt_new de,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    0 <= de < 2 * m ->
    0 <= Znth de to_new 0 < n.
Proof.
  intros n m from to wt g from_new to_new wt_new de
         Hgraph Hdir Hfrom_range Hto_range Hde.
  pose proof (array_graph_edge_count _ _ _ _ _ _ Hgraph) as Hcount.
  unfold directed_array_graph, directed_array_graph_prefix in Hdir.
  destruct Hdir as [_ [_ [_ [_ Hdata]]]].
  assert (Hhalf: 0 <= de / 2 < m).
  {
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  }
  assert (Hhalf_count: 0 <= de / 2 < graph_edge_count g) by lia.
  specialize (Hdata (de / 2) Hhalf_count).
  destruct Hdata as [_ [Hto_even [_ [_ [Hto_odd _]]]]].
  pose proof (Z.div_mod de 2 ltac:(lia)) as Hdivmod.
  pose proof (Z.mod_pos_bound de 2 ltac:(lia)) as Hmod_bound.
  assert (de mod 2 = 0 \/ de mod 2 = 1) as [Hmod | Hmod] by lia.
  - replace de with (2 * (de / 2)) by lia.
    rewrite Hto_even.
    unfold array_graph in Hgraph.
    destruct Hgraph as [_ [_ [_ [_ [_ [_ [_ Hedges]]]]]]].
    specialize (Hedges (de / 2)).
    assert (Hin: In (de / 2) (Zrange 0 m)).
    { rewrite <- In_Zrange; exact Hhalf. }
    specialize (Hedges Hin).
    destruct Hedges as [_ [Hto _]].
    rewrite Hto.
    apply Hto_range; exact Hhalf.
  - replace de with (2 * (de / 2) + 1) by lia.
    rewrite Hto_odd.
    unfold array_graph in Hgraph.
    destruct Hgraph as [_ [_ [_ [_ [_ [_ [_ Hedges]]]]]]].
    specialize (Hedges (de / 2)).
    assert (Hin: In (de / 2) (Zrange 0 m)).
    { rewrite <- In_Zrange; exact Hhalf. }
    specialize (Hedges Hin).
    destruct Hedges as [Hfrom _].
    rewrite Hfrom.
    apply Hfrom_range; exact Hhalf.
Qed.

(** * 基于有向边编号的 first/link 邻接表 *)

(** [is_link_chain link cur l] 表示从 cur 开始沿着 link 走，
    检查是否恰好走出有向边编号列表 l，并且最后在 -1 处结束。
    [is_first_link_chain] 则从 [Znth v first 0] 开始走这条链。 *)

Inductive is_link_chain (link : list DE) : DE -> list DE -> Prop :=
| is_link_chain_nil :
    is_link_chain link (-1) nil
| is_link_chain_cons :
    forall cur l,
      cur <> -1 ->                        
      is_link_chain link (Znth cur link 0) l ->
      is_link_chain link cur (cur :: l).


Definition is_first_link_chain
    (link first : list DE) (v : V) (l : list DE) : Prop :=
  is_link_chain link (Znth v first 0) l.

(**在已插入邻接表的有向边中，起点是v的所有有向边*)
Definition inserted_vertex_directed_edges
    (de_bound : DE) (from_new : list DE) (v : V) : list DE :=
  filter
    (fun de =>
      if Z.eq_dec (Znth de from_new 0) v then true else false)
    (Zrange 0 de_bound).

Definition vertex_directed_edges
    (g : G) (from_new : list DE) (v : V) : list DE :=
  inserted_vertex_directed_edges (2 * graph_edge_count g) from_new v.

Lemma inserted_vertex_directed_edges_In :
  forall de_bound from_new v de,
    In de (inserted_vertex_directed_edges de_bound from_new v) <->
    In de (Zrange 0 de_bound) /\ Znth de from_new 0 = v.
Proof.
  intros de_bound from_new v de.
  unfold inserted_vertex_directed_edges.
  rewrite filter_In.
  split.
  - intros [Hin Hfilter].
    split; [exact Hin |].
    destruct (Z.eq_dec (Znth de from_new 0) v); [exact e | discriminate].
  - intros [Hin Heq].
    split; [exact Hin |].
    destruct (Z.eq_dec (Znth de from_new 0) v); [reflexivity | congruence].
Qed.

Lemma vertex_directed_edges_In :
  forall g from_new v de,
    In de (vertex_directed_edges g from_new v) <->
    In de (Zrange 0 (2 * graph_edge_count g)) /\ Znth de from_new 0 = v.
Proof.
  intros g from_new v de.
  unfold vertex_directed_edges.
  apply inserted_vertex_directed_edges_In.
Qed.

Lemma vertex_directed_edges_range :
  forall g from_new v de,
    In de (vertex_directed_edges g from_new v) ->
    0 <= de < 2 * graph_edge_count g.
Proof.
  intros g from_new v de Hde.
  apply vertex_directed_edges_In in Hde.
  destruct Hde as [Hrange _].
  rewrite <- In_Zrange in Hrange.
  exact Hrange.
Qed.

Lemma vertex_directed_edges_to_graph_vertex :
  forall n m from to wt g from_new to_new wt_new v de,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    In de (vertex_directed_edges g from_new v) ->
    In (Znth de to_new 0) (graph_vertices g).
Proof.
  intros n m from to wt g from_new to_new wt_new v de
         Hgraph Hdir Hfrom_range Hto_range Hde.
  pose proof (array_graph_edge_count _ _ _ _ _ _ Hgraph) as Hcount.
  assert (Hde_range_g : 0 <= de < 2 * graph_edge_count g)
    by (eapply vertex_directed_edges_range; eauto).
  assert (Hde_range_m : 0 <= de < 2 * m) by lia.
  apply array_graph_vertex_in with (n := n) (m := m) (from := from) (to := to) (wt := wt).
  - exact Hgraph.
  - eapply directed_array_graph_to_range; eauto.
Qed.

Lemma vertex_directed_edges_weight_lt :
  forall n m from to wt g from_new to_new wt_new v de inf,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    (forall e, 0 <= e < m -> Znth e wt 0 < inf) ->
    In de (vertex_directed_edges g from_new v) ->
    Znth de wt_new 0 < inf.
Proof.
  intros n m from to wt g from_new to_new wt_new v de inf
         Hgraph Hdir Hwt_range Hde.
  pose proof (array_graph_edge_count _ _ _ _ _ _ Hgraph) as Hcount.
  assert (Hde_range_g : 0 <= de < 2 * graph_edge_count g)
    by (eapply vertex_directed_edges_range; eauto).
  assert (Hhalf_m : 0 <= de / 2 < m).
  {
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  }
  pose proof (directed_array_graph_weight
    g from_new to_new wt_new de Hdir Hde_range_g) as Hweight.
  unfold weight, edge_weight_instance in Hweight.
  inversion Hweight as [Hweight_eq].
  unfold array_graph in Hgraph.
  destruct Hgraph as [_ [_ [_ [_ [_ [_ [_ Hdata]]]]]]].
  assert (Hin_half : In (de / 2) (Zrange 0 m)).
  {
    rewrite <- In_Zrange.
    exact Hhalf_m.
  }
  specialize (Hdata (de / 2) Hin_half).
  destruct Hdata as [_ [_ Hgraph_weight]].
  rewrite Hgraph_weight.
  apply Hwt_range.
  exact Hhalf_m.
Qed.

Lemma directed_edge_for_graph_step :
  forall n m from to wt g from_new to_new wt_new e u v,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    step_aux g e u v ->
    exists de,
      In de (vertex_directed_edges g from_new u) /\
      Znth de to_new 0 = v /\
      de / 2 = e.
Proof.
  intros n m from to wt g from_new to_new wt_new e u v
         Hgraph Hdir Hstep.
  pose proof (array_graph_edge_count _ _ _ _ _ _ Hgraph) as Hcount.
  unfold step_aux, graph_instance, graph_step in Hstep.
  destruct Hstep as [Hevalid [_ Hends]].
  assert (He_range : 0 <= e < m).
  {
    unfold edge_valid in Hevalid.
    unfold array_graph in Hgraph.
    destruct Hgraph as [_ [Hedges _]].
    rewrite Hedges in Hevalid.
    rewrite <- In_Zrange in Hevalid.
    exact Hevalid.
  }
  assert (He_count : 0 <= e < graph_edge_count g) by lia.
  unfold directed_array_graph, directed_array_graph_prefix in Hdir.
  destruct Hdir as [_ [_ [_ [_ Hdata]]]].
  specialize (Hdata e He_count).
  destruct Hdata as
    [Hfrom_even [Hto_even [_ [Hfrom_odd [Hto_odd _]]]]].
  destruct Hends as [[Hu Hv] | [Hu Hv]]; subst.
  - exists (2 * e).
    split.
    + rewrite vertex_directed_edges_In.
      split.
      * rewrite <- In_Zrange.
        lia.
      * rewrite Hfrom_even.
        reflexivity.
    + split.
      * rewrite Hto_even.
        reflexivity.
      * rewrite Z.mul_comm.
        apply Z.div_mul; lia.
  - exists (2 * e + 1).
    split.
    + rewrite vertex_directed_edges_In.
      split.
      * rewrite <- In_Zrange.
        lia.
      * rewrite Hfrom_odd.
        reflexivity.
    + split.
      * rewrite Hto_odd.
        reflexivity.
      * replace (2 * e + 1) with (e * 2 + 1) by lia.
        rewrite Z.div_add_l by lia.
        replace (1 / 2) with 0 by reflexivity.
        lia.
Qed.

(**已插入de_bound条有向边，检验first link的邻接表是否能表达此时所有点的出边*)
Definition first_link_matches_inserted_vertex_directed_edges
    (g : G) (de_bound : DE) (from_new : list DE) (first link : list DE) : Prop :=
  Zlength first = Zlength (graph_vertices g) /\
  Zlength link = 2 * graph_edge_count g /\
  0 <= de_bound <= Zlength link /\
  forall v,
    In v (graph_vertices g) ->
    exists cl : list DE,
      is_first_link_chain link first v cl /\
      Permutation cl (inserted_vertex_directed_edges de_bound from_new v).

Lemma first_link_matches_inserted_vertex_directed_edges_empty :
  forall g from_new first link,
    Zlength first = Zlength (graph_vertices g) ->
    Zlength link = 2 * graph_edge_count g ->
    (forall v, In v (graph_vertices g) -> Znth v first 0 = -1) ->
    first_link_matches_inserted_vertex_directed_edges
      g 0 from_new first link.
Proof.
  intros g from_new first link Hfirst_len Hlink_len Hfirst.
  unfold first_link_matches_inserted_vertex_directed_edges.
  split; [exact Hfirst_len |].
  split; [exact Hlink_len |].
  split; [split; [lia | apply Zlength_nonneg] |].
  intros v Hv.
  exists nil.
  split.
  - unfold is_first_link_chain.
    rewrite Hfirst by exact Hv.
    constructor.
  - unfold inserted_vertex_directed_edges.
    change (Zrange 0 0) with (@nil Z).
    simpl.
    reflexivity.
Qed.

Lemma Zrange_0_snoc :
  forall i,
    0 <= i ->
    Zrange 0 (i + 1) = Zrange 0 i ++ [i].
Proof.
  intros i Hi.
  unfold Zrange.
  replace (Z.to_nat (i + 1 - 0)) with (Z.to_nat (i - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app.
  replace (0 + Z.of_nat (Z.to_nat (i - 0))) with i by lia.
  simpl.
  reflexivity.
Qed.

Lemma inserted_vertex_directed_edges_snoc_same :
    forall i from_new u,
    0 <= i ->
    Znth i from_new 0 = u ->
    inserted_vertex_directed_edges (i + 1) from_new u =
    inserted_vertex_directed_edges i from_new u ++ [i].
Proof.
  intros i from_new u Hi Hu.
  unfold inserted_vertex_directed_edges.
  set (p := fun de : Z =>
    if Z.eq_dec (Znth de from_new 0) u then true else false).
  change (filter p (Zrange 0 (i + 1)) = filter p (Zrange 0 i) ++ [i]).
  rewrite Zrange_0_snoc by exact Hi.
  rewrite filter_app.
  simpl.
  assert (Hp: p i = true).
  { unfold p. destruct (Z.eq_dec (Znth i from_new 0) u); [reflexivity | congruence]. }
  rewrite Hp.
  reflexivity.
Qed.

Lemma inserted_vertex_directed_edges_snoc_diff :
    forall i from_new u v,
    0 <= i ->
    Znth i from_new 0 = u ->
    v <> u ->
    inserted_vertex_directed_edges (i + 1) from_new v =
    inserted_vertex_directed_edges i from_new v.
Proof.
  intros i from_new u v Hi Hu Hneq.
  unfold inserted_vertex_directed_edges.
  set (p := fun de : Z =>
    if Z.eq_dec (Znth de from_new 0) v then true else false).
  change (filter p (Zrange 0 (i + 1)) = filter p (Zrange 0 i)).
  rewrite Zrange_0_snoc by exact Hi.
  rewrite filter_app.
  simpl.
  assert (Hp: p i = false).
  { unfold p. destruct (Z.eq_dec (Znth i from_new 0) v); [congruence | reflexivity]. }
  rewrite Hp.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma inserted_vertex_directed_edges_range :
  forall de_bound from_new v de,
    In de (inserted_vertex_directed_edges de_bound from_new v) ->
    0 <= de < de_bound.
Proof.
  intros de_bound from_new v de Hde.
  apply inserted_vertex_directed_edges_In in Hde.
  destruct Hde as [Hrange _].
  rewrite <- In_Zrange in Hrange.
  exact Hrange.
Qed.

Lemma is_link_chain_replace_fresh :
  forall link fresh old_next cur l,
    is_link_chain link cur l ->
    0 <= fresh < Zlength link ->
    (forall de, In de l -> 0 <= de < fresh) ->
    is_link_chain (replace_Znth fresh old_next link) cur l.
Proof.
  intros link fresh old_next cur l Hchain Hfresh Hrange.
  induction Hchain.
  - constructor.
  - constructor.
    + exact H.
    + replace (Znth cur (replace_Znth fresh old_next link) 0)
        with (Znth cur link 0).
      * apply IHHchain.
        intros de Hde.
        apply Hrange.
        simpl; right; exact Hde.
      * symmetry.
        apply Znth_replace_Znth_diff_local.
        -- exact Hfresh.
        -- pose proof (Hrange cur ltac:(simpl; left; reflexivity)) as Hcur_range.
           destruct Hfresh as [_ Hfresh_len].
           destruct Hcur_range as [Hcur_nonneg Hcur_lt].
           split; [exact Hcur_nonneg |].
           eapply Z.lt_trans; eauto.
        -- pose proof (Hrange cur ltac:(simpl; left; reflexivity)) as Hcur_range.
           destruct Hcur_range as [_ Hcur_lt].
           intro Heq; subst fresh; lia.
Qed.

Lemma first_link_matches_inserted_vertex_directed_edges_insert :
  forall g de_bound from_new first link u,
    first_link_matches_inserted_vertex_directed_edges
      g de_bound from_new first link ->
    In u (graph_vertices g) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength first) ->
    0 <= de_bound < Zlength link ->
    Znth de_bound from_new 0 = u ->
    first_link_matches_inserted_vertex_directed_edges
      g (de_bound + 1) from_new
      (replace_Znth u de_bound first)
      (replace_Znth de_bound (Znth u first 0) link).
Proof.
  intros g de_bound from_new first link u Hmatch Hu Hvrange Hde Hfrom.
  unfold first_link_matches_inserted_vertex_directed_edges in *.
  destruct Hmatch as [Hfirst_len [Hlink_len [Hbound Hmatch]]].
  split.
  - rewrite Zlength_replace_Znth_local; exact Hfirst_len.
  - split.
    + rewrite Zlength_replace_Znth_local; exact Hlink_len.
    + split.
      * rewrite Zlength_replace_Znth_local. lia.
      * intros v Hv.
    specialize (Hmatch v Hv) as [cl [Hchain Hperm]].
    assert (Hcl_range: forall de, In de cl -> 0 <= de < de_bound).
    {
      intros de Hde_in.
      apply inserted_vertex_directed_edges_range
        with (from_new := from_new) (v := v).
      eapply Permutation_in; [exact Hperm | exact Hde_in].
    }
    destruct (Z.eq_dec v u) as [Heq | Hneq].
    {
      subst v.
      exists (de_bound :: cl).
      split.
      - unfold is_first_link_chain in *.
        rewrite Znth_replace_Znth_same_local by (apply Hvrange; exact Hu).
        constructor; [lia |].
        rewrite Znth_replace_Znth_same_local by exact Hde.
        apply is_link_chain_replace_fresh.
        + exact Hchain.
        + exact Hde.
        + exact Hcl_range.
      - rewrite inserted_vertex_directed_edges_snoc_same by
          (try lia; exact Hfrom).
        eapply Permutation_trans.
        + apply perm_skip; exact Hperm.
        + apply Permutation_cons_append.
    }
    {
      exists cl.
      split.
      - unfold is_first_link_chain in *.
        rewrite Znth_replace_Znth_diff_local.
        + apply is_link_chain_replace_fresh.
          * exact Hchain.
          * exact Hde.
          * exact Hcl_range.
        + apply Hvrange; exact Hu.
        + apply Hvrange; exact Hv.
        + lia.
      - assert (Hinsert_diff:
            inserted_vertex_directed_edges (de_bound + 1) from_new v =
            inserted_vertex_directed_edges de_bound from_new v).
        {
          apply inserted_vertex_directed_edges_snoc_diff with (u := u).
          - lia.
          - exact Hfrom.
          - exact Hneq.
        }
        rewrite Hinsert_diff.
        exact Hperm.
    }
Qed.

Definition first_link_matches_vertex_directed_edges
    (g : G) (from_new : list DE) (first link : list DE) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    exists cl : list DE,
      is_first_link_chain link first v cl /\
      Permutation cl (vertex_directed_edges g from_new v).

Lemma first_link_matches_inserted_vertex_directed_edges_finish :
  forall g from_new first link,
    first_link_matches_inserted_vertex_directed_edges
      g (2 * graph_edge_count g) from_new first link ->
    first_link_matches_vertex_directed_edges g from_new first link.
Proof.
  intros g from_new first link Hmatch.
  unfold first_link_matches_inserted_vertex_directed_edges in Hmatch.
  unfold first_link_matches_vertex_directed_edges, vertex_directed_edges.
  destruct Hmatch as [_ [_ [_ Hmatch]]].
  intros v Hv.
  apply Hmatch; exact Hv.
Qed.


Definition growing_subgraph_state (g: G) (s:St) : Prop :=
  gvalid s.(Prim.graph_in_state) /\
  connected s.(Prim.graph_in_state) /\
  subgraph2 s.(Prim.graph_in_state) g.

Lemma initSt_growing_subgraph_state :
  forall n m from to wt g src,
    array_graph n m from to wt g ->
    In src (graph_vertices g) ->
    growing_subgraph_state g (initSt g src).
Proof.
  intros n m from to wt g src Hgraph Hsrc.
  split.
  - apply empty_graph_valid_of.
  - split.
    + intros x y Hx Hy.
      apply initSt_vvalid in Hx.
      apply initSt_vvalid in Hy.
      subst.
      unfold reachable.
      reflexivity.
    + constructor.
      * intros x Hx.
        apply initSt_vvalid in Hx.
        subst; exact Hsrc.
      * intros x y e Hstep.
        unfold initSt in Hstep.
        simpl in Hstep.
        unfold empty_graph_of, step_aux, graph_instance, graph_step in Hstep.
        simpl in Hstep.
        destruct Hstep as [He _].
        contradiction.
Qed.

Lemma reachable_crosses_outside_vertex :
  forall g s x y,
    growing_subgraph_state g s ->
    connected g ->
    vvalid s.(Prim.graph_in_state) x ->
    vvalid g y ->
    ~ vvalid s.(Prim.graph_in_state) y ->
    exists e, Prim.is_cut_edge g s e.
Proof.
  intros g s x y Hgrow Hconn Hx_s Hy_g Hy_not_s.
  destruct Hgrow as [_ [_ Hsub]].
  destruct Hsub as [Hsub_vertex _].
  pose proof (Hsub_vertex x Hx_s) as Hx_g.
  pose proof (Hconn x y Hx_g Hy_g) as Hreach.
  unfold reachable in Hreach.
  induction_1n Hreach.
  - contradiction.
  - destruct H as [e Hstep].
    destruct (classic (vvalid s.(Prim.graph_in_state) x0)) as [Hx0_s | Hx0_out].
    + apply IHrt; auto.
    + exists e.
      exists x, x0.
      split; [exact Hx_s |].
      split; [exact Hx0_out | exact Hstep].
Qed.

Lemma array_graph_outside_subgraph_state_vertex :
  forall n m from to wt g s,
    array_graph n m from to wt g ->
    gvalid s.(Prim.graph_in_state) ->
    subgraph2 s.(Prim.graph_in_state) g ->
    state_vertex_count s < n ->
    exists y,
      In y (graph_vertices g) /\
      ~ vvalid s.(Prim.graph_in_state) y.
Proof.
  intros n m from to wt g s Hgraph Hvalid_s Hsub Hlt.
  pose proof (array_graph_vertex_count _ _ _ _ _ _ Hgraph) as Hlen_g.
  destruct Hgraph as [Hvertices _].
  destruct Hsub as [Hsub_vertex _].
  destruct (classic (exists y,
    In y (graph_vertices g) /\
    ~ vvalid s.(Prim.graph_in_state) y)) as [Hex | Hnone].
  - exact Hex.
  - exfalso.
    assert (Hall_g_in_s :
      forall y, In y (graph_vertices g) -> vvalid s.(Prim.graph_in_state) y).
    {
      intros y Hy.
      destruct (classic (vvalid s.(Prim.graph_in_state) y)) as [Hy_s | Hy_s].
      - exact Hy_s.
      - exfalso. apply Hnone. exists y. split; auto.
    }
    assert (Hperm :
      Permutation (bijective_listV s.(Prim.graph_in_state)) (graph_vertices g)).
    {
      apply NoDup_Permutation.
      - apply bijective_listV_NoDup. exact Hvalid_s.
      - rewrite Hvertices. apply NoDup_Zrange.
      - intros y.
        rewrite bijective_vertices by exact Hvalid_s.
        split.
        + intros Hy_s.
          pose proof (Hsub_vertex y Hy_s) as Hy_g.
          change (In y (graph_vertices g)) in Hy_g.
          exact Hy_g.
        + apply Hall_g_in_s.
    }
    apply Permutation_length in Hperm.
    unfold state_vertex_count, vertex_num in Hlt.
    rewrite !Zlength_correct in Hlt.
    rewrite Hperm in Hlt.
    rewrite <- Zlength_correct in Hlt.
    rewrite Hlen_g in Hlt.
    lia.
Qed.

Lemma has_cut_edge_exists_by_state_vertex_count :
  forall n m from to wt g s,
    array_graph n m from to wt g ->
    connected g ->
    growing_subgraph_state g s ->
    (exists x, vvalid s.(Prim.graph_in_state) x) ->
    state_vertex_count s < n ->
    exists e, Prim.is_cut_edge g s e.
Proof.
  intros n m from to wt g s Hgraph Hconn Hgrow [x Hx_s] Hlt.
  destruct Hgrow as [Hvalid_s [Hconn_s Hsub]].
  assert (Hgrow : growing_subgraph_state g s).
  { split; [exact Hvalid_s |].
    split; [exact Hconn_s | exact Hsub]. }
  destruct (array_graph_outside_subgraph_state_vertex
    n m from to wt g s Hgraph Hvalid_s Hsub Hlt) as [y [Hy_g Hy_not_s]].
  eapply (reachable_crosses_outside_vertex g s x y); eauto.
Qed.

Definition visited_matches_state (g: G)(s: St) (visited : list Z) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    (Znth v visited 0 <> 0 <-> vvalid s.(Prim.graph_in_state) v).

    
(** edge_parent 中已经加入生长图的点对应合法的有向边编号。 *)
Definition parent_edges_range_state
    (g : G) (src : V) (s : St) (edge_parent : list DE) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    v <> src ->
    vvalid s.(Prim.graph_in_state) v ->
    0 <= Znth v edge_parent 0 < 2 * graph_edge_count g.

(** edge_parent 精确枚举当前生长图中的边。
    对当前生长图中的每条无向边 e，它必须来自某个非源、已加入顶点 v
    记录的有向父边 edge_parent[v]；反过来，每个这样的父边也必须在生长图中有效。 *)
Definition parent_edges_exact_state
    (g : G) (src : V) (s : St) (edge_parent : list DE) : Prop :=
  forall e,
    evalid s.(Prim.graph_in_state) e <->
    exists v,
      In v (graph_vertices g) /\
      v <> src /\
      vvalid s.(Prim.graph_in_state) v /\
      e = Znth v edge_parent 0 / 2.

(** edge_parent 是否真实描述当前生长图的父边集合。 *)
Definition parent_edges_match_state
    (g : G) (src : V) (s : St) (edge_parent : list DE) : Prop :=
  vvalid s.(Prim.graph_in_state) src /\
  parent_edges_range_state g src s edge_parent /\
  parent_edges_exact_state g src s edge_parent.

Lemma NoDup_incl_length_lt_local :
  forall {A : Type} (l1 l2 : list A) x,
    NoDup l1 ->
    incl l1 l2 ->
    In x l2 ->
    ~ In x l1 ->
    (length l1 < length l2)%nat.
Proof.
  intros A l1 l2 x Hnodup Hincl Hx Hnotin.
  assert (Hnodup_cons : NoDup (x :: l1)).
  { constructor; auto. }
  assert (Hincl_cons : incl (x :: l1) l2).
  {
    intros y [Hy | Hy].
    - subst; exact Hx.
    - apply Hincl; exact Hy.
  }
  pose proof (NoDup_incl_length Hnodup_cons Hincl_cons) as Hlen.
  simpl in Hlen.
  lia.
Qed.

Lemma completed_growing_subgraph_vvalid :
  forall n m from to wt g s v,
    array_graph n m from to wt g ->
    growing_subgraph_state g s ->
    state_vertex_count s = n ->
    In v (graph_vertices g) ->
    vvalid s.(Prim.graph_in_state) v.
Proof.
  intros n m from to wt g s v Hgraph Hgrow Hcount Hv_g.
  destruct Hgrow as [Hvalid_s [_ Hsub]].
  destruct Hsub as [Hsub_vertex _].
  destruct (classic (vvalid s.(Prim.graph_in_state) v)) as [Hv_s | Hv_not_s].
  - exact Hv_s.
  - exfalso.
    pose proof (array_graph_vertex_count _ _ _ _ _ _ Hgraph) as Hlen_g.
    assert (Hnodup_s :
      NoDup (bijective_listV s.(Prim.graph_in_state))).
    { apply bijective_listV_NoDup; exact Hvalid_s. }
    assert (Hincl :
      incl (bijective_listV s.(Prim.graph_in_state)) (graph_vertices g)).
    {
      intros x Hx.
      rewrite bijective_vertices in Hx by exact Hvalid_s.
      pose proof (Hsub_vertex x Hx) as Hx_g.
      change (In x (graph_vertices g)) in Hx_g.
      exact Hx_g.
    }
    assert (Hnotin :
      ~ In v (bijective_listV s.(Prim.graph_in_state))).
    {
      intro Hv_list.
      rewrite bijective_vertices in Hv_list by exact Hvalid_s.
      contradiction.
    }
    pose proof (NoDup_incl_length_lt_local
      (bijective_listV s.(Prim.graph_in_state))
      (graph_vertices g) v Hnodup_s Hincl Hv_g Hnotin) as Hlt.
    apply Nat2Z.inj_lt in Hlt.
    rewrite <- !Zlength_correct in Hlt.
    unfold state_vertex_count, vertex_num in Hcount.
    rewrite Hcount in Hlt.
    rewrite Hlen_g in Hlt.
    lia.
Qed.

Lemma parent_edges_match_state_all_range :
  forall n m from to wt g src s edge_parent v,
    array_graph n m from to wt g ->
    growing_subgraph_state g s ->
    state_vertex_count s = n ->
    parent_edges_match_state g src s edge_parent ->
    0 <= v < n ->
    v <> src ->
    0 <= Znth v edge_parent 0 < 2 * m.
Proof.
  intros n m from to wt g src s edge_parent v
         Hgraph Hgrow Hcount Hparent Hv_range Hv_not_src.
  pose proof (array_graph_edge_count _ _ _ _ _ _ Hgraph) as Hedge_count.
  assert (Hv_g : In v (graph_vertices g)).
  { eapply array_graph_vertex_in; eauto. }
  pose proof (completed_growing_subgraph_vvalid
    n m from to wt g s v Hgraph Hgrow Hcount Hv_g) as Hv_s.
  destruct Hparent as [_ [Hparent_range _]].
  pose proof (Hparent_range v Hv_g Hv_not_src Hv_s) as Hrange.
  rewrite Hedge_count in Hrange.
  exact Hrange.
Qed.

(** 判断是否是指向外部点v的割边 *)

Definition is_cut_edge_to_vertex (g : G) (s : St) (v : V) (e : E) : Prop :=
  ~ vvalid s.(Prim.graph_in_state) v /\
  (edge_src g e = v \/ edge_dst g e = v) /\
  Prim.is_cut_edge g s e.

Lemma visited_nonzero_not_cut_edge_to_vertex :
  forall g s visited v e,
    visited_matches_state g s visited ->
    In v (graph_vertices g) ->
    Znth v visited 0 <> 0 ->
    ~ is_cut_edge_to_vertex g s v e.
Proof.
  intros g s visited v e Hvisited Hv_graph Hvisited_nonzero Hcut.
  unfold is_cut_edge_to_vertex in Hcut.
  destruct Hcut as [Hv_not_valid _].
  destruct (Hvisited v Hv_graph) as [Hvisited_to_valid _].
  apply Hv_not_valid.
  apply Hvisited_to_valid.
  exact Hvisited_nonzero.
Qed.

Lemma directed_edge_is_cut_edge_to_vertex :
  forall g s from_new to_new wt_new de,
    directed_array_graph g from_new to_new wt_new ->
    gvalid g ->
    0 <= de < 2 * graph_edge_count g ->
    edge_valid g (de / 2) ->
    vvalid s.(Prim.graph_in_state) (Znth de from_new 0) ->
    ~ vvalid s.(Prim.graph_in_state) (Znth de to_new 0) ->
    is_cut_edge_to_vertex g s (Znth de to_new 0) (de / 2).
Proof.
  intros g s from_new to_new wt_new de Hdir Hg Hde Hedge Hfrom_valid Hto_not_valid.
  pose proof (directed_array_graph_step
    g from_new to_new wt_new de Hdir Hg Hde Hedge) as Hstep.
  pose proof Hstep as Hstep_for_endpoint.
  split; [exact Hto_not_valid |].
  split.
  - unfold step_aux, graph_instance, graph_step in Hstep_for_endpoint.
    destruct Hstep_for_endpoint as [_ [_ [[Hsrc Hdst] | [Hdst Hsrc]]]].
    + right; symmetry; exact Hdst.
    + left; symmetry; exact Hsrc.
  - exists (Znth de from_new 0), (Znth de to_new 0).
    split; [exact Hfrom_valid |].
    split; [exact Hto_not_valid | exact Hstep].
Qed.

(**判断是否是指向外部点v的最小割边*)
Definition is_min_cut_edge_to_vertex (g : G) (s : St) (v : V) (e : E) : Prop :=
  min_object_of_subset Z_op_le
    (fun e => is_cut_edge_to_vertex g s v e)
    (weight g)
    e.

(** 判断点v目前是否已经有了加入生长子图的最小代价以及实现这个代价的边 *)
Definition vertex_has_parent_edge
    (g : G) (s : St) (lowcost:list Z) ( edge_parent : list DE) (inf : Z) (v : V) : Prop :=
  let de := Znth v edge_parent 0 in
  de <> -1 /\
  0 <= de < 2 * graph_edge_count g /\
  Znth v lowcost 0 < inf /\
  is_min_cut_edge_to_vertex g s v (de / 2) /\
  weight g (de / 2) = Some (Znth v lowcost 0).

(**判断点v是否是与生长子图相邻的侯选点*)
Definition candidate_vertex
    (g : G) (s : St) (lowcost:list Z) (edge_parent : list DE) (inf : Z) (v : V) : Prop :=
  In v (graph_vertices g) /\
  ~ vvalid s.(Prim.graph_in_state) v /\
  vertex_has_parent_edge g s lowcost edge_parent inf v.

Definition candidate_vertex_exists_in_range
    (n : Z) (g : G) (s : St)
    (lowcost:list Z) (edge_parent : list DE) (inf : Z) : Prop :=
  exists v,
    In v (Zrange 0 n) /\
    candidate_vertex g s lowcost edge_parent inf v.


(*有可能扫描到第j个点还没有找到候选点，如果找到了候选点，要求其lowcost当前最小*)  
Definition min_vertex_in_range
    (g : G) (s : St)
    (j inf :Z) (minIndex :V) (lowcost:list Z) (edge_parent : list DE) : Prop :=
  (minIndex = -1 /\
   forall v,
     In v (Zrange 0 j) ->
     ~ candidate_vertex g s lowcost edge_parent inf v) \/
  (candidate_vertex g s lowcost edge_parent inf minIndex /\
   In minIndex (Zrange 0 j) /\
   min_object_of_subset Z_op_le
	     (fun v =>
	        In v (Zrange 0 j) /\
	         candidate_vertex g s lowcost edge_parent inf v)
		     (fun v => Some (Znth v lowcost 0))
		     minIndex).

Lemma min_vertex_in_range_empty :
  forall g s inf lowcost edge_parent,
    min_vertex_in_range g s 0 inf (-1) lowcost edge_parent.
Proof.
  intros g s inf lowcost edge_parent.
  left.
  split; [reflexivity |].
  intros v Hv _.
  rewrite <- In_Zrange in Hv.
  lia.
Qed.

Lemma min_vertex_in_range_not_minus_one :
  forall n g s inf minIndex lowcost edge_parent,
    candidate_vertex_exists_in_range n g s lowcost edge_parent inf ->
    min_vertex_in_range g s n inf minIndex lowcost edge_parent ->
    minIndex <> -1.
Proof.
  intros n g s inf minIndex lowcost edge_parent Hexists Hmin.
  destruct Hexists as [v [Hv_in Hcand]].
  destruct Hmin as [[HminIndex_none Hnone] | [_ [HminIndex_in _]]].
  - subst minIndex.
    specialize (Hnone v Hv_in).
    contradiction.
  - rewrite <- In_Zrange in HminIndex_in.
    lia.
Qed.

     (*判断edge_parent【minIndex】储存的确实是当前生长子图s的所有割边里最小的*)
Definition selected_parent_edge_is_min_cut_edge
    (g : G) (s : St) (edge_parent : list DE) (minIndex : V) : Prop :=
  min_object_of_subset Z_op_le
    (fun e => Prim.is_cut_edge g s e)
    (weight g)
    (Znth minIndex edge_parent 0 / 2).

(*找出Prim.v里x <- get (fun s '(u, v) => vvalid s.(graph_in_state) u /\ ~ vvalid s.(graph_in_state) v /\ step_aux g e u v)要求的序对*)
Definition selected_parent_pair
    (g : G) (s : St)
    (from_new to_new edge_parent : list DE)
    (minIndex u v : V) : Prop :=
  let e := Znth minIndex edge_parent 0 / 2 in
  v = minIndex /\
  vvalid s.(Prim.graph_in_state) u /\
  ~ vvalid s.(Prim.graph_in_state) v /\
  step_aux g e u v.

(*加边状态更新*)
Definition selected_parent_add_to_mst
    (g : G) (s s_next : St)
    (from_new to_new edge_parent : list DE)
    (minIndex : V) : Prop :=
  exists u v,
    selected_parent_pair g s from_new to_new edge_parent minIndex u v /\
    addEdge s.(Prim.graph_in_state) s_next.(Prim.graph_in_state)
      u v (Znth minIndex edge_parent 0 / 2).

Lemma selected_parent_add_to_mst_vvalid :
  forall g s s_next from_new to_new edge_parent minIndex x,
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    (vvalid s_next.(Prim.graph_in_state) x <->
     vvalid s.(Prim.graph_in_state) x \/ x = minIndex).
Proof.
  intros g s s_next from_new to_new edge_parent minIndex x Hadd.
  destruct Hadd as [u [v [Hpair Hadd]]].
  destruct Hpair as [Hv_eq [Hu_valid [_ _]]].
  subst v.
  destruct Hadd as [Hadd_vvalid _ _].
  rewrite Hadd_vvalid.
  split.
  - intros [Hx | [Hx | Hx]].
    + left; exact Hx.
    + subst x; left; exact Hu_valid.
    + right; exact Hx.
  - intros [Hx | Hx].
    + left; exact Hx.
    + right; right; exact Hx.
Qed.

Lemma selected_parent_add_to_mst_old_vvalid :
  forall g s s_next from_new to_new edge_parent minIndex x,
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    vvalid s.(Prim.graph_in_state) x ->
    vvalid s_next.(Prim.graph_in_state) x.
Proof.
  intros g s s_next from_new to_new edge_parent minIndex x Hadd Hx.
  rewrite (selected_parent_add_to_mst_vvalid
    g s s_next from_new to_new edge_parent minIndex x Hadd).
  left; exact Hx.
Qed.

Lemma selected_parent_add_to_mst_minIndex_vvalid :
  forall g s s_next from_new to_new edge_parent minIndex,
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    vvalid s_next.(Prim.graph_in_state) minIndex.
Proof.
  intros g s s_next from_new to_new edge_parent minIndex Hadd.
  rewrite (selected_parent_add_to_mst_vvalid
    g s s_next from_new to_new edge_parent minIndex minIndex Hadd).
  right; reflexivity.
Qed.

Lemma selected_parent_add_to_mst_state_vertex_count :
  forall g s s_next from_new to_new edge_parent minIndex,
    growing_subgraph_state g s ->
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    state_vertex_count s_next = state_vertex_count s + 1.
Proof.
  intros g s s_next from_new to_new edge_parent minIndex Hstate Hadd.
  destruct Hadd as [u [v [Hpair Hadd]]].
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [_ [Hu [Hvout _]]].
  assert (Hs_valid : gvalid s.(Prim.graph_in_state)) by exact (proj1 Hstate).
  assert (Hnext_valid : gvalid s_next.(Prim.graph_in_state)).
  { eapply addEdge_gvalid; eauto. }
  assert (Hperm :
    Permutation (bijective_listV s_next.(Prim.graph_in_state))
      (v :: bijective_listV s.(Prim.graph_in_state))).
  {
    eapply (addEdge_vlist_permutation
      s.(Prim.graph_in_state) s_next.(Prim.graph_in_state)
      u v (Znth minIndex edge_parent 0 / 2) Hu Hvout Hadd).
    - apply bijective_listV_NoDup; exact Hs_valid.
    - intros x; apply bijective_vertices; exact Hs_valid.
    - apply bijective_listV_NoDup; exact Hnext_valid.
    - intros x; apply bijective_vertices; exact Hnext_valid.
  }
  unfold state_vertex_count, vertex_num.
  apply Permutation_length in Hperm.
  do 2 rewrite Zlength_correct.
  rewrite Hperm.
  simpl; lia.
Qed.

Lemma selected_parent_add_to_mst_parent_edges_match :
  forall g src s s_next from_new to_new edge_parent minIndex,
    parent_edges_match_state g src s edge_parent ->
    In minIndex (graph_vertices g) ->
    0 <= Znth minIndex edge_parent 0 < 2 * graph_edge_count g ->
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    parent_edges_match_state g src s_next edge_parent.
Proof.
  intros g src s s_next from_new to_new edge_parent minIndex
         Hmatch Hmin_graph Hparent_range Hadd0.
  destruct Hmatch as [Hsrc [Hrange Hexact]].
  destruct Hadd0 as [u [v [Hpair Hadd]]].
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [Hv_eq [Hu [Hvout _]]].
  subst v.
  destruct Hadd as [Hadd_vvalid Hadd_evalid _].
  assert (Hmin_not_src : minIndex <> src).
  {
    intros Hcontra.
    subst minIndex.
    apply Hvout; exact Hsrc.
  }
  split.
  - apply Hadd_vvalid.
    left; exact Hsrc.
  - split.
    + intros x Hx_graph Hx_src Hx_next.
      apply Hadd_vvalid in Hx_next.
      destruct Hx_next as [Hx_old | [Hx_u | Hx_min]].
      * eapply Hrange; eauto.
      * subst x. eapply Hrange; eauto.
      * subst x. exact Hparent_range.
    + intros e.
      split.
      * intros He_next.
        apply Hadd_evalid in He_next.
        destruct He_next as [He_old | He_new].
        -- apply Hexact in He_old.
           destruct He_old as [x [Hx_graph [Hx_src [Hx_old Heq]]]].
           exists x.
           repeat split; try assumption.
           apply Hadd_vvalid.
           left; exact Hx_old.
        -- exists minIndex.
           split; [exact Hmin_graph |].
           split; [exact Hmin_not_src |].
           split.
           ++ apply Hadd_vvalid.
              right; right; reflexivity.
           ++ exact He_new.
      * intros [x [Hx_graph [Hx_src [Hx_next Heq]]]].
        apply Hadd_evalid.
        apply Hadd_vvalid in Hx_next.
        destruct Hx_next as [Hx_old | [Hx_u | Hx_min]].
        -- left.
           apply Hexact.
           exists x; repeat split; assumption.
        -- subst x.
           left.
           apply Hexact.
           exists u; repeat split; assumption.
        -- subst x.
           right; exact Heq.
Qed.

Lemma selected_parent_add_to_mst_still_outside :
  forall g s s_next from_new to_new edge_parent minIndex x,
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    ~ vvalid s.(Prim.graph_in_state) x ->
    x <> minIndex ->
    ~ vvalid s_next.(Prim.graph_in_state) x.
Proof.
  intros g s s_next from_new to_new edge_parent minIndex x Hadd Hx Hneq.
  rewrite (selected_parent_add_to_mst_vvalid
    g s s_next from_new to_new edge_parent minIndex x Hadd).
  intros [Hold | Hnew]; [apply Hx; exact Hold | apply Hneq; exact Hnew].
Qed.

Lemma cut_edge_not_evalid_in_state :
  forall g s u v e,
    gvalid g ->
    growing_subgraph_state g s ->
    vvalid s.(Prim.graph_in_state) u ->
    ~ vvalid s.(Prim.graph_in_state) v ->
    step_aux g e u v ->
    ~ evalid s.(Prim.graph_in_state) e.
Proof.
  intros g s u v e Hg Hstate Hu Hvout Hstep Heold.
  destruct Hstate as [Hsvalid [_ Hsub]].
  destruct Hsub as [_ Hsub_step].
  destruct (no_empty_edge s.(Prim.graph_in_state) e Hsvalid Heold)
    as [x [y Hstep_old]].
  pose proof (Hsub_step x y e Hstep_old) as Hstep_g_old.
  pose proof (step_aux_unique_undirected g e u v x y Hg Hstep Hstep_g_old)
    as [[Hx Hy] | [Hx Hy]]; subst.
  - apply Hvout. eapply step_vvalid2; eauto.
  - apply Hvout. eapply step_vvalid1; eauto.
Qed.

Lemma is_cut_edge_to_vertex_pair :
  forall g s from_new to_new edge_parent minIndex,
    is_cut_edge_to_vertex g s minIndex (Znth minIndex edge_parent 0 / 2) ->
    exists u,
      selected_parent_pair
        g s from_new to_new edge_parent minIndex u minIndex.
Proof.
  intros g s from_new to_new edge_parent minIndex Hcut_to.
  destruct Hcut_to as [Hout [Hendpoint Hcut]].
  destruct Hcut as [u [v [Hu [Hv Hstep]]]].
  exists u.
  unfold selected_parent_pair.
  split; [reflexivity|].
  split; [exact Hu|].
  split; [exact Hout|].
  unfold step_aux, graph_instance, graph_step in Hstep.
  destruct Hstep as [He [Hends [[Hu_eq Hv_eq] | [Hu_eq Hv_eq]]]]; subst.
  - destruct Hendpoint as [Hsrc | Hdst].
    + exfalso. apply Hout. unfold edge_src in Hsrc. rewrite <- Hsrc. exact Hu.
    + exact (conj He (conj Hends (or_introl (conj eq_refl (eq_sym Hdst))))).
  - destruct Hendpoint as [Hsrc | Hdst].
    + exact (conj He (conj Hends (or_intror (conj eq_refl (eq_sym Hsrc))))).
    + exfalso. apply Hout. unfold edge_dst in Hdst. rewrite <- Hdst. exact Hu.
Qed.

Lemma selected_parent_add_to_mst_exists :
  forall n m from to wt g s from_new to_new lowcost edge_parent minIndex,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    growing_subgraph_state g s ->
    min_vertex_in_range g s n 1000000000 minIndex lowcost edge_parent ->
    minIndex <> -1 ->
    exists u v s_next,
      selected_parent_pair
        g s from_new to_new edge_parent minIndex u v /\
      selected_parent_add_to_mst
        g s s_next from_new to_new edge_parent minIndex /\
      state_vertex_count s_next = state_vertex_count s + 1.
Proof.
  intros n m from to wt g s from_new to_new lowcost edge_parent minIndex
         Hgraph Hfrom_valid Hto_valid Hstate Hmin_vertex HminIndex.
  assert (Hg : gvalid g).
  { eapply array_graph_gvalid; eauto. }
  destruct Hmin_vertex as [[Hminus _] | [Hcand _]]; [contradiction|].
  destruct Hcand as [_ [Houtside Hparent]].
  destruct Hparent as [_ [_ [_ [Hmin_edge_to Hweight]]]].
  destruct Hmin_edge_to as [Hcut_to _].
  destruct (is_cut_edge_to_vertex_pair
    g s from_new to_new edge_parent minIndex Hcut_to) as [u Hpair].
  exists u, minIndex.
  exists (@Prim.mkSt_s G
    (add_edge_graph s.(Prim.graph_in_state)
      u minIndex (Znth minIndex edge_parent 0 / 2))).
  split; [exact Hpair|].
  split.
  - exists u, minIndex.
    split; [exact Hpair|].
    unfold selected_parent_pair in Hpair.
    destruct Hpair as [_ [Hu [Hvout Hstep]]].
    simpl.
    apply add_edge_graph_addEdge_any.
    + exact (proj1 Hstate).
    + eapply cut_edge_not_evalid_in_state; eauto.
  - unfold state_vertex_count.
    simpl.
    unfold selected_parent_pair in Hpair.
    destruct Hpair as [_ [Hu [Hvout _]]].
    rewrite add_edge_graph_vertex_num_new_vertex.
    + reflexivity.
    + exact (proj1 Hstate).
    + exact Hu.
    + exact Hvout.
Qed.

Lemma selected_parent_add_to_mst_visited_matches :
  forall n m from to wt g s s_next from_new to_new edge_parent minIndex visited,
    array_graph n m from to wt g ->
    Zlength visited = n ->
    In minIndex (graph_vertices g) ->
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    visited_matches_state g s visited ->
    visited_matches_state g s_next (replace_Znth minIndex 1 visited).
Proof.
  intros n m from to wt g s s_next from_new to_new edge_parent minIndex visited
         Hgraph Hlen Hmin_graph Hadd Hvisited.
  unfold visited_matches_state in *.
  intros x Hx_graph.
  rewrite (selected_parent_add_to_mst_vvalid
    g s s_next from_new to_new edge_parent minIndex x Hadd).
  destruct (Z.eq_dec x minIndex) as [Hx_eq | Hx_neq].
  - subst x.
    assert (Hrange : 0 <= minIndex < n).
    { eapply array_graph_vertex_range; eauto. }
    rewrite Znth_replace_Znth_same_local by (rewrite Hlen; exact Hrange).
    split; intros _; [right; reflexivity | lia].
  - assert (Hrange_x : 0 <= x < n).
    { eapply array_graph_vertex_range; eauto. }
    assert (Hrange_min : 0 <= minIndex < n).
    { eapply array_graph_vertex_range; eauto. }
    assert (Hrange_x_len : 0 <= x < Zlength visited) by (rewrite Hlen; lia).
    assert (Hrange_min_len : 0 <= minIndex < Zlength visited) by (rewrite Hlen; lia).
    rewrite (Znth_replace_Znth_diff_local
      visited minIndex x 1 Hrange_min_len Hrange_x_len
      ltac:(intro Heq; apply Hx_neq; symmetry; exact Heq)).
    rewrite Hvisited by exact Hx_graph.
    split; intros H.
    + left; exact H.
    + destruct H as [H | H]; [exact H | contradiction].
Qed.

Lemma addEdge_connected_preserve :
  forall h h' u v e,
    gvalid h ->
    gvalid h' ->
    connected h ->
    vvalid h u ->
    addEdge h h' u v e ->
    connected h'.
Proof.
  intros h h' u v e Hhvalid Hhvalid' Hconn Hu Hadd x y Hx Hy.
  destruct Hadd as [Hvalid _ Hstep].
  assert (Hsub : subgraph h h').
  {
    unfold subgraph.
    intros a b ee Hs.
    apply Hstep.
    left; exact Hs.
  }
  assert (Hlift : forall a b, reachable h a b -> reachable h' a b).
  {
    intros a b Hr.
    eapply (sub_reachable h h' (g_valid1 := Hhvalid) Hsub).
    exact Hr.
  }
  apply Hvalid in Hx as [Hx_old | [Hx_u | Hx_v]];
  apply Hvalid in Hy as [Hy_old | [Hy_u | Hy_v]];
  subst.
  - apply Hlift. apply Hconn; auto.
  - apply Hlift. apply Hconn; auto.
  - eapply reachable_step_reachable with (y := u).
    + apply Hlift. apply Hconn; auto.
    + exists e. apply Hstep. right. split; [reflexivity | auto].
  - apply Hlift. apply Hconn; auto.
  - unfold reachable. reflexivity.
  - apply step_rt. exists e. apply Hstep. right. split; [reflexivity | auto].
  - eapply step_reachable_reachable with (y := u).
    + exists e. apply Hstep. right. split; [reflexivity | auto].
    + apply Hlift. apply Hconn; auto.
  - apply step_rt. exists e. apply Hstep. right. split; [reflexivity | auto].
  - unfold reachable. reflexivity.
Qed.

Lemma selected_parent_add_to_mst_growing :
  forall g s s_next from_new to_new edge_parent minIndex,
    growing_subgraph_state g s ->
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    growing_subgraph_state g s_next.
Proof.
  intros g s s_next from_new to_new edge_parent minIndex Hstate Hadd.
  destruct Hstate as [Hsvalid [Hconn Hsub]].
  destruct Hadd as [u [v [Hpair Hadd]]].
  destruct Hpair as [Hv_eq [Hu [Hvout Hstep_g]]].
  subst v.
  assert (Hsnextvalid : gvalid s_next.(Prim.graph_in_state)).
  { eapply addEdge_gvalid; eauto. }
  split.
  - exact Hsnextvalid.
  - split.
    + eapply (addEdge_connected_preserve
        s.(Prim.graph_in_state) s_next.(Prim.graph_in_state)
        u minIndex (Znth minIndex edge_parent 0 / 2));
        eauto.
    + constructor.
      * intros x Hx.
        destruct Hadd as [Hadd_vvalid _ _].
        apply Hadd_vvalid in Hx as [Hx | [Hx | Hx]].
        -- exact (subgraph2_vertex _ _ Hsub x Hx).
        -- subst x. exact (step_vvalid1 g (Znth minIndex edge_parent 0 / 2) u minIndex Hstep_g).
        -- subst x. exact (step_vvalid2 g (Znth minIndex edge_parent 0 / 2) u minIndex Hstep_g).
      * intros x y e Hxy.
        destruct Hadd as [_ _ Hadd_step].
        apply Hadd_step in Hxy as [Hxy_old | [Heq Hxy_new]].
        -- exact (subgraph2_step_aux _ _ Hsub x y e Hxy_old).
        -- subst e.
           destruct Hxy_new as [[-> ->] | [-> ->]].
           ++ exact Hstep_g.
           ++ apply step_sym. exact Hstep_g.
Qed.

Lemma cut_edge_witness_after_add_old :
  forall g s s_next from_new to_new edge_parent minIndex u v e,
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    v <> minIndex ->
    vvalid s.(Prim.graph_in_state) u ->
    ~ vvalid s.(Prim.graph_in_state) v ->
    step_aux g e u v ->
    Prim.is_cut_edge g s_next e.
Proof.
  intros g s s_next from_new to_new edge_parent minIndex u v e
         Hadd Hneq Hu Hv Hstep.
  exists u, v.
  split.
  - eapply selected_parent_add_to_mst_old_vvalid; eauto.
  - split.
    + eapply selected_parent_add_to_mst_still_outside; eauto.
    + exact Hstep.
Qed.

Lemma is_cut_edge_to_vertex_after_add_oriented :
  forall g s s_next from_new to_new edge_parent minIndex u v e,
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    v <> minIndex ->
    vvalid s.(Prim.graph_in_state) u ->
    ~ vvalid s.(Prim.graph_in_state) v ->
    step_aux g e u v ->
    (edge_src g e = v \/ edge_dst g e = v) ->
    is_cut_edge_to_vertex g s_next v e.
Proof.
  intros g s s_next from_new to_new edge_parent minIndex u v e
         Hadd Hneq Hu Hv Hstep Hendpoint.
  split.
  - eapply selected_parent_add_to_mst_still_outside; eauto.
	  - split; [exact Hendpoint |].
	    eapply cut_edge_witness_after_add_old; eauto.
Qed.

Lemma is_cut_edge_to_vertex_after_add_cases :
  forall n m from to wt g s s_next from_new to_new wt_new edge_parent minIndex v e,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    is_cut_edge_to_vertex g s_next v e ->
    is_cut_edge_to_vertex g s v e \/
    exists de,
      In de (vertex_directed_edges g from_new minIndex) /\
      Znth de to_new 0 = v /\
      de / 2 = e.
Proof.
  intros n m from to wt g s s_next from_new to_new wt_new
         edge_parent minIndex v e Hgraph Hdir Hadd Hcut.
  unfold is_cut_edge_to_vertex in Hcut.
  destruct Hcut as [Hvout_next [Hendpoint Hcut]].
  destruct Hcut as [u [w [Hu_next [Hwout_next Hstep]]]].
  pose proof (selected_parent_add_to_mst_vvalid
    g s s_next from_new to_new edge_parent minIndex u Hadd) as Hu_next_iff.
  apply Hu_next_iff in Hu_next as [Hu_old | Hu_new].
  - left.
    assert (Hvout_old : ~ vvalid s.(Prim.graph_in_state) v).
    {
      intro Hv_old.
      apply Hvout_next.
      eapply selected_parent_add_to_mst_old_vvalid; eauto.
    }
    split; [exact Hvout_old |].
    split; [exact Hendpoint |].
    exists u, v.
    split; [exact Hu_old |].
    split; [exact Hvout_old |].
    assert (Hw_eq_v : w = v).
    {
      pose proof Hstep as Hstep_dir.
      unfold graph_step in Hstep_dir.
      destruct Hstep_dir as [_ [_ Huw]].
      destruct Huw as [[Hu_eq Hw_eq] | [Hu_eq Hw_eq]];
        subst u w;
        destruct Hendpoint as [Hv_eq | Hv_eq];
        unfold edge_src, edge_dst in *; subst v; try reflexivity;
        exfalso; apply Hvout_old; exact Hu_old.
    }
    subst w.
    exact Hstep.
  - right.
    subst u.
    assert (Hw_eq_v : w = v).
    {
      pose proof Hstep as Hstep_dir.
      unfold graph_step in Hstep_dir.
      destruct Hstep_dir as [_ [_ Huw]].
      destruct Huw as [[Hu_eq Hw_eq] | [Hu_eq Hw_eq]];
        subst minIndex w;
        destruct Hendpoint as [Hv_eq | Hv_eq];
        unfold edge_src, edge_dst in *; subst v; try reflexivity;
        exfalso; apply Hvout_next;
        eapply selected_parent_add_to_mst_minIndex_vvalid; eauto.
    }
    subst w.
    eapply directed_edge_for_graph_step; eauto.
Qed.

(** * 扫描一条邻接表来更新 lowcost/parent *)

(** 这些谓词抽象 C 程序最后一层内循环：
    沿着被选中点的 [first/link] 链遍历所有出有向边，
    并用这些边更新 [lowcost] 和 [edge_parent]。 *)

(**判断沿邻接表扫描一条边后的更新操作是否正确，如果被扫描边确实是该边终点加入生长子图s割边且圈中比lowcost记录的小就更新，否则都不更新，*)
Definition scan_one_directed_edge_update
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z)
    (lowcost_in:list Z) (edge_parent_in : list DE)
    (de : DE)
    (lowcost_out:list Z) (edge_parent_out : list DE) : Prop :=
  let v := Znth de to_new 0 in
  let w := Znth de wt_new 0 in
  (is_cut_edge_to_vertex g s_next v (de / 2) /\
   w < Znth v lowcost_in 0 /\
   lowcost_out = replace_Znth v w lowcost_in /\
   edge_parent_out = replace_Znth v de edge_parent_in) \/
  ((~ is_cut_edge_to_vertex g s_next v (de / 2) \/
    Znth v lowcost_in 0 <= w) /\
   lowcost_out = lowcost_in /\
   edge_parent_out = edge_parent_in).

Lemma scan_one_directed_edge_update_other_vertex :
  forall g s_next to_new wt_new
         lowcost_in edge_parent_in de
         lowcost_out edge_parent_out x,
    scan_one_directed_edge_update
      g s_next to_new wt_new
	      lowcost_in edge_parent_in de
	      lowcost_out edge_parent_out ->
    0 <= Znth de to_new 0 < Zlength lowcost_in ->
    0 <= Znth de to_new 0 < Zlength edge_parent_in ->
    0 <= x < Zlength lowcost_in ->
    0 <= x < Zlength edge_parent_in ->
    x <> Znth de to_new 0 ->
    Znth x lowcost_out 0 = Znth x lowcost_in 0 /\
    Znth x edge_parent_out 0 = Znth x edge_parent_in 0.
Proof.
  intros g s_next to_new wt_new
         lowcost_in edge_parent_in de
         lowcost_out edge_parent_out x
         Hscan Hto_low Hto_parent Hx_low Hx_parent Hneq.
  unfold scan_one_directed_edge_update in Hscan.
  destruct Hscan as
    [[_ [_ [Hlow_out Hparent_out]]] |
     [_ [Hlow_out Hparent_out]]];
    subst lowcost_out edge_parent_out.
  - split.
    + eapply Znth_replace_Znth_diff_local.
      * exact Hto_low.
      * exact Hx_low.
      * lia.
    + eapply Znth_replace_Znth_diff_local.
      * exact Hto_parent.
      * exact Hx_parent.
      * lia.
  - split; reflexivity.
Qed.

Lemma scan_one_directed_edge_update_lengths :
  forall g s_next to_new wt_new
         lowcost_in edge_parent_in de
         lowcost_out edge_parent_out,
    scan_one_directed_edge_update
      g s_next to_new wt_new
      lowcost_in edge_parent_in de
      lowcost_out edge_parent_out ->
    Zlength lowcost_out = Zlength lowcost_in /\
    Zlength edge_parent_out = Zlength edge_parent_in.
Proof.
  intros g s_next to_new wt_new
         lowcost_in edge_parent_in de
         lowcost_out edge_parent_out Hscan.
  unfold scan_one_directed_edge_update in Hscan.
  destruct Hscan as
    [[_ [_ [Hlow_out Hparent_out]]] |
     [_ [Hlow_out Hparent_out]]];
    subst lowcost_out edge_parent_out;
    split;
    try reflexivity;
    rewrite Zlength_replace_Znth_local;
    reflexivity.
Qed.

Lemma scan_one_directed_edge_update_target :
  forall g s_next to_new wt_new
         lowcost_in edge_parent_in de
         lowcost_out edge_parent_out,
    scan_one_directed_edge_update
      g s_next to_new wt_new
      lowcost_in edge_parent_in de lowcost_out edge_parent_out ->
    0 <= Znth de to_new 0 < Zlength lowcost_in ->
    0 <= Znth de to_new 0 < Zlength edge_parent_in ->
    (is_cut_edge_to_vertex g s_next (Znth de to_new 0) (de / 2) /\
     Znth de wt_new 0 < Znth (Znth de to_new 0) lowcost_in 0 /\
     Znth (Znth de to_new 0) lowcost_out 0 = Znth de wt_new 0 /\
     Znth (Znth de to_new 0) edge_parent_out 0 = de) \/
    ((~ is_cut_edge_to_vertex g s_next (Znth de to_new 0) (de / 2) \/
      Znth (Znth de to_new 0) lowcost_in 0 <= Znth de wt_new 0) /\
     lowcost_out = lowcost_in /\
     edge_parent_out = edge_parent_in).
Proof.
  intros g s_next to_new wt_new
         lowcost_in edge_parent_in de lowcost_out edge_parent_out
         Hscan Hrange_low Hrange_parent.
  unfold scan_one_directed_edge_update in Hscan.
  destruct Hscan as
    [[Hcut [Hlt [Hlow_out Hparent_out]]] |
     [Hno_update [Hlow_out Hparent_out]]].
  - left.
    subst lowcost_out edge_parent_out.
    split; [exact Hcut |].
    split; [exact Hlt |].
    split.
    + apply Znth_replace_Znth_same_local.
      exact Hrange_low.
    + apply Znth_replace_Znth_same_local.
      exact Hrange_parent.
	  - right.
	    auto.
Qed.

(** 扫描一串有向边后的数组更新关系。
    参数顺序：
    [scanned_edges] 是已经扫描的有向边列表；
    [lowcost_before] / [edge_parent_before] 是扫描前的数组抽象值；
    [lowcost_after] / [edge_parent_after] 是扫描完这些边后的数组抽象值。
    递归扫描一条邻接表 *)
Inductive scan_directed_edges_update
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z) :
    list DE -> list Z -> list DE -> list Z -> list DE -> Prop :=
| scan_directed_edges_update_nil :
    forall lowcost edge_parent,
      scan_directed_edges_update
        g s_next to_new wt_new nil
        lowcost edge_parent lowcost edge_parent
| scan_directed_edges_update_cons :
    forall de rest
           lowcost0 edge_parent0
           lowcost1 edge_parent1
           lowcost2 edge_parent2,
      scan_one_directed_edge_update
        g s_next to_new wt_new
        lowcost0 edge_parent0 de lowcost1 edge_parent1 ->
      scan_directed_edges_update
        g s_next to_new wt_new rest
        lowcost1 edge_parent1 lowcost2 edge_parent2 ->
      scan_directed_edges_update
        g s_next to_new wt_new (de :: rest)
        lowcost0 edge_parent0 lowcost2 edge_parent2.

Lemma scan_directed_edges_update_app :
  forall g s_next to_new wt_new l1 l2
         lowcost0 edge_parent0
         lowcost1 edge_parent1
         lowcost2 edge_parent2,
    scan_directed_edges_update
      g s_next to_new wt_new l1
      lowcost0 edge_parent0 lowcost1 edge_parent1 ->
    scan_directed_edges_update
      g s_next to_new wt_new l2
      lowcost1 edge_parent1 lowcost2 edge_parent2 ->
    scan_directed_edges_update
      g s_next to_new wt_new (l1 ++ l2)
      lowcost0 edge_parent0 lowcost2 edge_parent2.
Proof.
  intros g s_next to_new wt_new l1 l2
         lowcost0 edge_parent0 lowcost1 edge_parent1
         lowcost2 edge_parent2 Hscan1 Hscan2.
  induction Hscan1.
  - simpl. exact Hscan2.
  - simpl.
    econstructor; eauto.
Qed.

Lemma is_link_chain_minus1_inv :
  forall link l,
    is_link_chain link (-1) l ->
    l = nil.
Proof.
  intros link l Hchain.
  inversion Hchain; subst; auto.
  contradiction.
Qed.

Definition scan_minIndex_adjacency_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (lowcost_after : list Z) (edge_parent_after : list DE) : Prop :=
  exists scanned_edges : list DE,
    is_first_link_chain link first minIndex scanned_edges /\
    Permutation scanned_edges (vertex_directed_edges g from_new minIndex) /\
    scan_directed_edges_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before
      lowcost_after edge_parent_after.

Definition scan_minIndex_adjacency_prefix_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V) (current_e : DE)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (lowcost_current : list Z) (edge_parent_current : list DE) : Prop :=
  exists scanned_edges remaining_edges : list DE,
    is_first_link_chain link first minIndex (scanned_edges ++ remaining_edges) /\
    is_link_chain link current_e remaining_edges /\
    Permutation (scanned_edges ++ remaining_edges)
      (vertex_directed_edges g from_new minIndex) /\
    scan_directed_edges_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before
      lowcost_current edge_parent_current.

Lemma scan_minIndex_adjacency_prefix_start :
  forall g s_next from_new first link to_new wt_new minIndex
         lowcost edge_parent,
    first_link_matches_vertex_directed_edges g from_new first link ->
    In minIndex (graph_vertices g) ->
    scan_minIndex_adjacency_prefix_update
      g s_next from_new first link to_new wt_new minIndex
      (Znth minIndex first 0)
      lowcost edge_parent lowcost edge_parent.
Proof.
  intros g s_next from_new first link to_new wt_new minIndex
         lowcost edge_parent Hmatch Hmin_graph.
  unfold scan_minIndex_adjacency_prefix_update.
  destruct (Hmatch minIndex Hmin_graph) as [cl [Hchain Hperm]].
  exists nil, cl.
  simpl.
  repeat split; auto.
  constructor.
Qed.

Lemma scan_minIndex_adjacency_prefix_step :
  forall g s_next from_new first link to_new wt_new minIndex current_e
         lowcost_before edge_parent_before
         lowcost_current edge_parent_current
         lowcost_next edge_parent_next,
    current_e <> -1 ->
    scan_minIndex_adjacency_prefix_update
      g s_next from_new first link to_new wt_new
      minIndex current_e
      lowcost_before edge_parent_before
      lowcost_current edge_parent_current ->
    scan_one_directed_edge_update
      g s_next to_new wt_new
      lowcost_current edge_parent_current
      current_e
      lowcost_next edge_parent_next ->
    scan_minIndex_adjacency_prefix_update
      g s_next from_new first link to_new wt_new
      minIndex (Znth current_e link 0)
      lowcost_before edge_parent_before
      lowcost_next edge_parent_next.
Proof.
  intros g s_next from_new first link to_new wt_new minIndex current_e
         lowcost_before edge_parent_before
         lowcost_current edge_parent_current
         lowcost_next edge_parent_next
         Hcur Hprefix Hone.
  destruct Hprefix as
    [scanned_edges [remaining_edges
      [Hchain [Hremaining [Hperm Hscan]]]]].
  inversion Hremaining; subst.
  - contradiction.
  - exists (scanned_edges ++ [current_e]), l.
    repeat split.
    + rewrite <- app_assoc. simpl.
      exact Hchain.
    + match goal with
      | H : is_link_chain link (Znth current_e link 0) _ |- _ => exact H
      end.
    + rewrite <- app_assoc. simpl.
      exact Hperm.
    + eapply scan_directed_edges_update_app.
      * exact Hscan.
      * simpl.
        econstructor; eauto.
        constructor.
Qed.

Lemma scan_minIndex_adjacency_prefix_current_in :
  forall g s_next from_new first link to_new wt_new minIndex current_e
         lowcost_before edge_parent_before
         lowcost_current edge_parent_current,
    current_e <> -1 ->
    scan_minIndex_adjacency_prefix_update
      g s_next from_new first link to_new wt_new
      minIndex current_e
      lowcost_before edge_parent_before
      lowcost_current edge_parent_current ->
    In current_e (vertex_directed_edges g from_new minIndex).
Proof.
  intros g s_next from_new first link to_new wt_new minIndex current_e
         lowcost_before edge_parent_before lowcost_current edge_parent_current
         Hcur Hprefix.
  destruct Hprefix as
    [scanned_edges [remaining_edges
      [_ [Hremaining [Hperm _]]]]].
  inversion Hremaining; subst; [contradiction |].
  eapply Permutation_in; [exact Hperm |].
  rewrite in_app_iff.
  right.
  simpl; left; reflexivity.
Qed.

Lemma scan_minIndex_adjacency_prefix_finish :
  forall g s_next from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before lowcost_after edge_parent_after,
    scan_minIndex_adjacency_prefix_update
      g s_next from_new first link to_new wt_new
      minIndex (-1)
      lowcost_before edge_parent_before
      lowcost_after edge_parent_after ->
    scan_minIndex_adjacency_update
      g s_next from_new first link to_new wt_new
      minIndex
      lowcost_before edge_parent_before
      lowcost_after edge_parent_after.
Proof.
  intros g s_next from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before lowcost_after edge_parent_after
         Hprefix.
  destruct Hprefix as
    [scanned_edges [remaining_edges
      [Hchain [Hremaining [Hperm Hscan]]]]].
  pose proof (is_link_chain_minus1_inv link remaining_edges Hremaining) as Hnil.
  subst remaining_edges.
  exists scanned_edges.
  rewrite app_nil_r in Hchain, Hperm.
  repeat split; auto.
Qed.

(** lowcost和edge_parent是否正确描述当前状态 *)

Definition lowcost_parent_match
    (g : G) (s : St)
    (lowcost:list Z) (edge_parent : list DE)
    (inf : Z) : Prop :=
  (forall v,
    In v (graph_vertices g) ->
    0 <= v < Zlength lowcost /\ 0 <= v < Zlength edge_parent) /\
  forall v,
	    In v (graph_vertices g) ->
	    ~ vvalid s.(Prim.graph_in_state) v ->
	    ((exists de,
		        Znth v edge_parent 0 = de /\
	        de <> -1 /\
	        0 <= de < 2 * graph_edge_count g /\
			        Znth v lowcost 0 < inf /\
	        is_min_cut_edge_to_vertex g s v (de / 2) /\
		        weight g (de / 2) = Some (Znth v lowcost 0)) \/
		     ((forall e, ~ is_cut_edge_to_vertex g s v e) /\
			      Znth v edge_parent 0 = -1 /\
			      Znth v lowcost 0 = inf)).

(** 参数化版本：把“点 v 当前可选的入树边集合”抽成 [edge_for_vertex]。
    后面扫描邻接表时会先维护这个泛化版本，最后再实例化回
    [is_cut_edge_to_vertex g s v]。 *)
Definition lowcost_parent_match_by
    (g : G)
    (eligible_vertex : V -> Prop)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost:list Z) (edge_parent : list DE)
    (inf : Z) : Prop :=
  (forall v,
    In v (graph_vertices g) ->
    0 <= v < Zlength lowcost /\ 0 <= v < Zlength edge_parent) /\
  forall v,
    In v (graph_vertices g) ->
    eligible_vertex v ->
    ((exists de,
        Znth v edge_parent 0 = de /\
        de <> -1 /\
        0 <= de < 2 * graph_edge_count g /\
        Znth v lowcost 0 < inf /\
        min_object_of_subset Z_op_le
          (edge_for_vertex v)
          (weight g)
          (de / 2) /\
        weight g (de / 2) = Some (Znth v lowcost 0)) \/
     ((forall e, ~ edge_for_vertex v e) /\
      Znth v edge_parent 0 = -1 /\
      Znth v lowcost 0 = inf)).

Lemma lowcost_parent_match_to_by :
  forall g s lowcost edge_parent inf,
    lowcost_parent_match g s lowcost edge_parent inf ->
    lowcost_parent_match_by
      g (fun v => ~ vvalid s.(Prim.graph_in_state) v)
      (fun v e => is_cut_edge_to_vertex g s v e)
      lowcost edge_parent inf.
Proof.
  intros g s lowcost edge_parent inf Hmatch.
  unfold lowcost_parent_match_by.
  destruct Hmatch as [Harray_range Hmatch].
  split; [exact Harray_range |].
  intros v Hv_graph Hv_out.
  apply Hmatch; auto.
Qed.

Lemma lowcost_parent_match_by_to :
  forall g s lowcost edge_parent inf,
    lowcost_parent_match_by
      g (fun v => ~ vvalid s.(Prim.graph_in_state) v)
      (fun v e => is_cut_edge_to_vertex g s v e)
      lowcost edge_parent inf ->
    lowcost_parent_match g s lowcost edge_parent inf.
Proof.
  intros g s lowcost edge_parent inf Hmatch.
  unfold lowcost_parent_match.
  destruct Hmatch as [Hrange Hmatch].
  split; [exact Hrange |].
  intros v Hv_graph Hv_out.
  specialize (Hmatch v Hv_graph Hv_out).
  exact Hmatch.
Qed.

Lemma init_lowcost_parent_match_by_empty :
  forall n m from to wt g src inf,
    array_graph n m from to wt g ->
    In src (graph_vertices g) ->
    lowcost_parent_match_by
      g
      (fun v => ~ vvalid (Prim.graph_in_state (initSt g src)) v)
      (fun _ _ => False)
      (replace_Znth src 0 (repeat inf (Z.to_nat n)))
      (repeat (-1) (Z.to_nat n))
      inf.
Proof.
  intros n m from to wt g src inf Hgraph Hsrc.
  unfold lowcost_parent_match_by.
  split.
  - intros v Hv_graph.
    assert (Hv_range : 0 <= v < n).
    {
      unfold array_graph in Hgraph.
      destruct Hgraph as [Hvertices _].
      rewrite Hvertices in Hv_graph.
      rewrite <- In_Zrange in Hv_graph.
      exact Hv_graph.
    }
    split.
    + rewrite Zlength_replace_Znth_local.
      rewrite Zlength_correct, repeat_length.
      rewrite Z2Nat.id by lia.
      exact Hv_range.
    + rewrite Zlength_correct, repeat_length.
      rewrite Z2Nat.id by lia.
      exact Hv_range.
  - intros v Hv_graph Hvout.
  assert (Hv_range : 0 <= v < n).
  {
    unfold array_graph in Hgraph.
    destruct Hgraph as [Hvertices _].
    rewrite Hvertices in Hv_graph.
    rewrite <- In_Zrange in Hv_graph.
    exact Hv_graph.
  }
  assert (Hsrc_range : 0 <= src < n).
  {
    unfold array_graph in Hgraph.
    destruct Hgraph as [Hvertices _].
    rewrite Hvertices in Hsrc.
    rewrite <- In_Zrange in Hsrc.
    exact Hsrc.
  }
	  right.
	  split.
	  + intros e Hfalse; exact Hfalse.
	  + split.
	    * rewrite Znth_repeat_lt.
	      -- reflexivity.
	      -- rewrite Z2Nat.id by lia.
	         exact Hv_range.
	    * assert (Hneq : v <> src).
	      {
	        intro Heq.
	        subst v.
        apply Hvout.
        apply initSt_vvalid.
        reflexivity.
	      }
	      rewrite Znth_replace_Znth_diff_local.
	      -- rewrite Znth_repeat_lt.
	         ++ reflexivity.
	         ++ rewrite Z2Nat.id by lia.
	            exact Hv_range.
	      -- rewrite Zlength_correct, repeat_length.
	         rewrite Z2Nat.id by lia.
	         exact Hsrc_range.
	      -- rewrite Zlength_correct, repeat_length.
	         rewrite Z2Nat.id by lia.
	         exact Hv_range.
	      -- lia.
Qed.

Lemma lowcost_parent_match_by_iff :
  forall g eligible1 eligible2 edge_for1 edge_for2 lowcost edge_parent inf,
    lowcost_parent_match_by g eligible1 edge_for1 lowcost edge_parent inf ->
    (forall v, In v (graph_vertices g) -> eligible2 v -> eligible1 v) ->
    (forall v e,
        In v (graph_vertices g) ->
        eligible2 v ->
        (edge_for1 v e <-> edge_for2 v e)) ->
    lowcost_parent_match_by g eligible2 edge_for2 lowcost edge_parent inf.
Proof.
  intros g eligible1 eligible2 edge_for1 edge_for2 lowcost edge_parent inf
         Hmatch Helig_impl Hedge_iff.
  unfold lowcost_parent_match_by in *.
  destruct Hmatch as [Hrange Hmatch].
  split; [exact Hrange |].
  intros v Hv_graph Helig2.
  specialize (Hmatch v Hv_graph (Helig_impl v Hv_graph Helig2)).
  destruct Hmatch as
    [[de [Hparent [Hde [Hde_range [Hlow [Hmin Hweight]]]]]]
    | [Hnone [Hparent Hlow]]].
  - left.
    exists de.
    split; [exact Hparent |].
    split; [exact Hde |].
    split; [exact Hde_range |].
    split; [exact Hlow |].
    split.
    + unfold min_object_of_subset in *.
      destruct Hmin as [Hedge_de Hmin].
      split.
      * apply (Hedge_iff v (de / 2) Hv_graph Helig2).
        exact Hedge_de.
      * intros e Hedge2.
        apply Hmin.
        apply (Hedge_iff v e Hv_graph Helig2).
        exact Hedge2.
    + exact Hweight.
  - right.
    split.
    + intros e Hedge2.
      apply (Hnone e).
      apply (Hedge_iff v e Hv_graph Helig2).
      exact Hedge2.
    + split; auto.
Qed.

Definition add_scanned_edge_for_vertex
    (g : G) (s_next : St) (to_new : list DE)
    (edge_for_vertex : V -> E -> Prop) (de : DE)
    (v : V) (e : E) : Prop :=
  edge_for_vertex v e \/
  (v = Znth de to_new 0 /\
   e = de / 2 /\
   is_cut_edge_to_vertex g s_next v e).

Fixpoint add_scanned_edges_for_vertex
    (g : G) (s_next : St) (to_new : list DE)
    (edge_for_vertex : V -> E -> Prop) (scanned_edges : list DE)
    : V -> E -> Prop :=
  match scanned_edges with
  | nil => edge_for_vertex
  | de :: rest =>
      add_scanned_edges_for_vertex
        g s_next to_new
        (add_scanned_edge_for_vertex g s_next to_new edge_for_vertex de)
        rest
  end.

Definition add_vertex_directed_edges_for_vertex
    (g : G) (s_next : St)
    (from_new to_new : list DE) (minIndex : V)
    (edge_for_vertex : V -> E -> Prop)
    (v : V) (e : E) : Prop :=
  edge_for_vertex v e \/
  exists de,
    In de (vertex_directed_edges g from_new minIndex) /\
    v = Znth de to_new 0 /\
    e = de / 2 /\
    is_cut_edge_to_vertex g s_next v e.

Lemma add_scanned_edges_for_vertex_spec :
  forall g s_next to_new edge_for_vertex scanned_edges v e,
    add_scanned_edges_for_vertex
      g s_next to_new edge_for_vertex scanned_edges v e <->
    edge_for_vertex v e \/
    exists de,
      In de scanned_edges /\
      v = Znth de to_new 0 /\
      e = de / 2 /\
      is_cut_edge_to_vertex g s_next v e.
Proof.
  intros g s_next to_new edge_for_vertex scanned_edges.
  revert edge_for_vertex.
  induction scanned_edges as [| de rest IH]; intros edge_for_vertex v e; simpl.
  - split.
    + intros H; left; exact H.
    + intros [H | [de [Hde _]]]; [exact H | inversion Hde].
  - rewrite IH.
    unfold add_scanned_edge_for_vertex.
    split.
    + intros [[Hbase | Hde] | [de' [Hin [Hv [He Hcut]]]]].
      * left; exact Hbase.
	      * right.
	        exists de.
	        simpl.
	        destruct Hde as [Hv [He Hcut]].
	        split; [left; reflexivity |].
	        split; [exact Hv |].
	        split; [exact He | exact Hcut].
	      * right.
	        exists de'.
	        simpl.
	        split; [right; exact Hin |].
	        split; [exact Hv |].
	        split; [exact He | exact Hcut].
    + intros [Hbase | [de' [Hin [Hv [He Hcut]]]]].
      * left; left; exact Hbase.
      * simpl in Hin.
        destruct Hin as [Heq | Hin].
	        -- subst de'.
	           left; right.
	           split; [exact Hv |].
	           split; [exact He | exact Hcut].
	        -- right.
	           exists de'.
	           split; [exact Hin |].
	           split; [exact Hv |].
	           split; [exact He | exact Hcut].
Qed.

Lemma add_scanned_edges_for_vertex_perm :
  forall g s_next from_new to_new minIndex edge_for_vertex scanned_edges,
    Permutation scanned_edges (vertex_directed_edges g from_new minIndex) ->
    forall v e,
      add_scanned_edges_for_vertex
        g s_next to_new edge_for_vertex scanned_edges v e <->
      add_vertex_directed_edges_for_vertex
        g s_next from_new to_new minIndex edge_for_vertex v e.
Proof.
  intros g s_next from_new to_new minIndex edge_for_vertex scanned_edges Hperm v e.
  rewrite add_scanned_edges_for_vertex_spec.
  unfold add_vertex_directed_edges_for_vertex.
  split.
  - intros [Hbase | [de [Hin [Hv [He Hcut]]]]].
    + left; exact Hbase.
	    + right.
	      exists de.
	      split.
	      * eapply Permutation_in; eauto.
	      * split; [exact Hv |].
	        split; [exact He | exact Hcut].
  - intros [Hbase | [de [Hin [Hv [He Hcut]]]]].
    + left; exact Hbase.
	    + right.
	      exists de.
	      split.
	      * eapply Permutation_in; [symmetry; exact Hperm | exact Hin].
      * split; [exact Hv |].
        split; [exact He | exact Hcut].
Qed.

Lemma selected_parent_add_to_mst_cut_edges_match :
  forall n m from to wt g s s_next from_new to_new wt_new edge_parent minIndex,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    selected_parent_add_to_mst
      g s s_next from_new to_new edge_parent minIndex ->
    forall v e,
      ~ vvalid s_next.(Prim.graph_in_state) v ->
      (add_vertex_directed_edges_for_vertex
        g s_next from_new to_new minIndex
        (fun v e => is_cut_edge_to_vertex g s v e)
        v e <->
       is_cut_edge_to_vertex g s_next v e).
Proof.
  intros n m from to wt g s s_next from_new to_new wt_new edge_parent minIndex
         Hgraph Hdir Hadd v e Hvout_next.
  split.
  - intros [Hold | [de [Hde [Hv [He Hcut]]]]].
    + unfold is_cut_edge_to_vertex in Hold.
      destruct Hold as [Hvout_old [Hendpoint Hcut_old]].
      destruct Hcut_old as [u [w [Hu_old [Hwout_old Hstep]]]].
      assert (Hw_eq_v : w = v).
      {
        pose proof Hstep as Hstep_dir.
        unfold graph_step in Hstep_dir.
        destruct Hstep_dir as [_ [_ Hends]].
        destruct Hends as [[Hu_eq Hw_eq] | [Hu_eq Hw_eq]];
          subst u w;
          destruct Hendpoint as [Hendpoint | Hendpoint];
          unfold edge_src, edge_dst in *; subst v; try reflexivity;
          exfalso; apply Hvout_old; exact Hu_old.
      }
      subst w.
      assert (Hneq : v <> minIndex).
      {
        intro Hvm.
        subst v.
        apply Hvout_next.
        eapply selected_parent_add_to_mst_minIndex_vvalid; eauto.
      }
      eapply is_cut_edge_to_vertex_after_add_oriented; eauto.
    + subst v e.
      exact Hcut.
  - intros Hcut_next.
    destruct (is_cut_edge_to_vertex_after_add_cases
      n m from to wt g s s_next from_new to_new wt_new edge_parent minIndex v e
      Hgraph Hdir Hadd Hcut_next) as [Hold | [de [Hde [Hv He]]]].
    + left; exact Hold.
    + right.
      exists de.
      split; [exact Hde |].
      split; [symmetry; exact Hv |].
      split; [symmetry; exact He |].
      exact Hcut_next.
Qed.

Lemma initSt_cut_edges_match :
  forall n m from to wt g src from_new to_new wt_new,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    forall v e,
      ~ vvalid (Prim.graph_in_state (initSt g src)) v ->
      (add_vertex_directed_edges_for_vertex
        g (initSt g src) from_new to_new src
        (fun _ _ => False) v e <->
       is_cut_edge_to_vertex g (initSt g src) v e).
Proof.
  intros n m from to wt g src from_new to_new wt_new Hgraph Hdir v e Hvout.
  split.
  - intros [Hfalse | [de [Hde [Hv [He Hcut]]]]].
    + contradiction.
    + subst v e.
      exact Hcut.
  - intros Hcut.
    unfold is_cut_edge_to_vertex in Hcut.
    destruct Hcut as [Hvout_cut [Hendpoint Hcut]].
    destruct Hcut as [u [w [Hu [Hwout Hstep]]]].
    apply initSt_vvalid in Hu.
    subst u.
    assert (Hw_eq_v : w = v).
    {
      pose proof Hstep as Hstep_dir.
      unfold graph_step in Hstep_dir.
      destruct Hstep_dir as [_ [_ Hends]].
      destruct Hends as [[Hu_eq Hw_eq] | [Hu_eq Hw_eq]];
        subst src w;
        destruct Hendpoint as [Hendpoint | Hendpoint];
        unfold edge_src, edge_dst in *; subst v; try reflexivity;
        exfalso; apply Hvout; apply initSt_vvalid; reflexivity.
    }
    subst w.
    right.
    destruct (directed_edge_for_graph_step
      n m from to wt g from_new to_new wt_new e src v
      Hgraph Hdir Hstep) as [de [Hde [Hto He]]].
    exists de.
    split; [exact Hde |].
    split; [symmetry; exact Hto |].
    split; [symmetry; exact He |].
    unfold is_cut_edge_to_vertex.
    split; [exact Hvout_cut |].
    split; [exact Hendpoint |].
    exists src, v.
    split.
    + apply initSt_vvalid; reflexivity.
    + split; [exact Hvout_cut | exact Hstep].
Qed.

Lemma scan_one_directed_edge_update_lowcost_parent_match_by :
  forall g s_next to_new wt_new
         eligible_vertex edge_for_vertex
         lowcost_in edge_parent_in de
         lowcost_out edge_parent_out inf,
    lowcost_parent_match_by
      g eligible_vertex edge_for_vertex
      lowcost_in edge_parent_in inf ->
    scan_one_directed_edge_update
      g s_next to_new wt_new
      lowcost_in edge_parent_in de
      lowcost_out edge_parent_out ->
    In (Znth de to_new 0) (graph_vertices g) ->
    0 <= de < 2 * graph_edge_count g ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_in) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_in) ->
    Znth de wt_new 0 < inf ->
    weight g (de / 2) = Some (Znth de wt_new 0) ->
    lowcost_parent_match_by
      g eligible_vertex
      (add_scanned_edge_for_vertex g s_next to_new edge_for_vertex de)
      lowcost_out edge_parent_out inf.
Proof.
  intros g s_next to_new wt_new eligible_vertex edge_for_vertex
         lowcost_in edge_parent_in de lowcost_out edge_parent_out inf
         Hmatch Hscan Htarget_graph Hde_range Hlow_range Hparent_range
         Hwt_inf Hweight_de.
	  unfold lowcost_parent_match_by in *.
  destruct Hmatch as [Harray_range Hmatch].
  destruct (scan_one_directed_edge_update_lengths
    g s_next to_new wt_new
    lowcost_in edge_parent_in de lowcost_out edge_parent_out Hscan)
    as [Hlow_len Hparent_len].
	  split.
	  { intros v Hv_graph.
	    destruct (Harray_range v Hv_graph) as [Hlow_v Hparent_v].
	    split; [rewrite Hlow_len; exact Hlow_v | rewrite Hparent_len; exact Hparent_v]. }
  intros v Hv_graph Helig.
  assert (Htarget_low : 0 <= Znth de to_new 0 < Zlength lowcost_in)
    by (apply Hlow_range; exact Htarget_graph).
  assert (Htarget_parent : 0 <= Znth de to_new 0 < Zlength edge_parent_in)
    by (apply Hparent_range; exact Htarget_graph).
  destruct (Z.eq_dec v (Znth de to_new 0)) as [Hv_eq | Hv_neq].
  - subst v.
    specialize (Hmatch (Znth de to_new 0) Htarget_graph Helig).
    destruct (scan_one_directed_edge_update_target
      g s_next to_new wt_new lowcost_in edge_parent_in de
      lowcost_out edge_parent_out Hscan Htarget_low Htarget_parent)
      as [[Hcut [Hlt [Hlow_out Hparent_out]]] |
          [Hno_update [Hlow_out Hparent_out]]].
    + left.
      exists de.
      split; [exact Hparent_out |].
      split; [lia |].
      split; [exact Hde_range |].
      split; [rewrite Hlow_out; exact Hwt_inf |].
      split.
      * unfold min_object_of_subset.
        split.
        -- unfold add_scanned_edge_for_vertex.
           right.
           split; [reflexivity |].
           split; [reflexivity | exact Hcut].
        -- intros e' Hedge'.
           unfold add_scanned_edge_for_vertex in Hedge'.
           destruct Hedge' as [Hold_edge | [_ [Heq Hnew_cut]]].
           ++ destruct Hmatch as
                [[de_old [_ [_ [_ [_ [Hmin_old Hweight_old]]]]]]
                | [Hnone_old _]].
              ** unfold min_object_of_subset in Hmin_old.
                 destruct Hmin_old as [_ Hmin_old].
                 eapply Z_op_le_trans
                   with (y := Some (Znth (Znth de to_new 0) lowcost_in 0)).
                 --- replace (weight g (de / 2))
                       with (Some (Znth de wt_new 0)) by (symmetry; exact Hweight_de).
                     simpl; lia.
	                 --- replace (Some (Znth (Znth de to_new 0) lowcost_in 0))
	                       with (weight g (de_old / 2))
	                       by exact Hweight_old.
                     apply Hmin_old; exact Hold_edge.
              ** exfalso; exact (Hnone_old e' Hold_edge).
           ++ subst e'.
              replace (weight g (de / 2))
                with (Some (Znth de wt_new 0)) by (symmetry; exact Hweight_de).
              apply Z_op_le_refl.
      * rewrite Hlow_out; exact Hweight_de.
    + destruct Hmatch as
        [[de_old [Hparent_old [Hde_old [Hrange_old [Hlow_old [Hmin_old Hweight_old]]]]]]
        | [Hnone_old [Hparent_old Hlow_old]]].
      * left.
        exists de_old.
        split; [rewrite Hparent_out; exact Hparent_old |].
        split; [exact Hde_old |].
        split; [exact Hrange_old |].
        split; [rewrite Hlow_out; exact Hlow_old |].
        split.
        -- unfold min_object_of_subset in *.
           destruct Hmin_old as [Hold_subset Hold_min].
           split.
           ++ unfold add_scanned_edge_for_vertex; left; exact Hold_subset.
           ++ intros e' Hedge'.
              unfold add_scanned_edge_for_vertex in Hedge'.
              destruct Hedge' as [Hold_edge | [_ [Heq Hnew_cut]]].
              ** exact (Hold_min e' Hold_edge).
              ** destruct Hno_update as [Hnot_cut | Hnot_better].
                 --- subst e'. contradiction.
                 --- replace (weight g (de_old / 2))
                       with (Some (Znth (Znth de to_new 0) lowcost_in 0))
                       by (symmetry; exact Hweight_old).
                     replace (weight g e')
                       with (Some (Znth de wt_new 0)).
                     2: { subst e'. symmetry; exact Hweight_de. }
                     simpl; exact Hnot_better.
        -- rewrite Hlow_out; exact Hweight_old.
      * right.
        split.
        -- intros e' Hedge'.
           unfold add_scanned_edge_for_vertex in Hedge'.
           destruct Hedge' as [Hold_edge | [_ [Heq Hnew_cut]]].
           ++ exact (Hnone_old e' Hold_edge).
           ++ subst e'.
              destruct Hno_update as [Hnot_cut | Hnot_better].
              ** exact (Hnot_cut Hnew_cut).
              ** rewrite Hlow_old in Hnot_better.
                 lia.
        -- split; [rewrite Hparent_out; exact Hparent_old |].
           rewrite Hlow_out; exact Hlow_old.
  - specialize (Hmatch v Hv_graph Helig).
    assert (Hv_low : 0 <= v < Zlength lowcost_in)
      by (apply Hlow_range; exact Hv_graph).
    assert (Hv_parent : 0 <= v < Zlength edge_parent_in)
      by (apply Hparent_range; exact Hv_graph).
    destruct (scan_one_directed_edge_update_other_vertex
      g s_next to_new wt_new
      lowcost_in edge_parent_in de
      lowcost_out edge_parent_out v
      Hscan Htarget_low Htarget_parent Hv_low Hv_parent Hv_neq)
      as [Hlow_out_v Hparent_out_v].
    destruct Hmatch as
      [[de_old [Hparent_old [Hde_old [Hrange_old [Hlow_old [Hmin_old Hweight_old]]]]]]
      | [Hnone_old [Hparent_old Hlow_old]]].
    + left.
      exists de_old.
      split; [rewrite Hparent_out_v; exact Hparent_old |].
      split; [exact Hde_old |].
      split; [exact Hrange_old |].
      split; [rewrite Hlow_out_v; exact Hlow_old |].
      split.
      * unfold min_object_of_subset in *.
        destruct Hmin_old as [Hold_subset Hold_min].
        split.
        -- unfold add_scanned_edge_for_vertex; left; exact Hold_subset.
        -- intros e' Hedge'.
           unfold add_scanned_edge_for_vertex in Hedge'.
           destruct Hedge' as [Hold_edge | [Hv_target [_ _]]].
           ++ exact (Hold_min e' Hold_edge).
           ++ contradiction.
      * rewrite Hlow_out_v; exact Hweight_old.
    + right.
      split.
      * intros e' Hedge'.
        unfold add_scanned_edge_for_vertex in Hedge'.
        destruct Hedge' as [Hold_edge | [Hv_target [_ _]]].
        -- exact (Hnone_old e' Hold_edge).
        -- contradiction.
  * split; [rewrite Hparent_out_v; exact Hparent_old |].
        rewrite Hlow_out_v; exact Hlow_old.
Qed.

Lemma scan_directed_edges_update_lowcost_parent_match_by :
  forall g s_next to_new wt_new scanned_edges
         eligible_vertex edge_for_vertex
         lowcost_in edge_parent_in lowcost_out edge_parent_out inf,
    lowcost_parent_match_by
      g eligible_vertex edge_for_vertex
      lowcost_in edge_parent_in inf ->
    scan_directed_edges_update
      g s_next to_new wt_new scanned_edges
      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_in) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_in) ->
    (forall de,
        In de scanned_edges ->
        In (Znth de to_new 0) (graph_vertices g)) ->
    (forall de,
        In de scanned_edges ->
        0 <= de < 2 * graph_edge_count g) ->
    (forall de,
        In de scanned_edges ->
        Znth de wt_new 0 < inf) ->
    (forall de,
        In de scanned_edges ->
        weight g (de / 2) = Some (Znth de wt_new 0)) ->
    lowcost_parent_match_by
      g eligible_vertex
      (add_scanned_edges_for_vertex
        g s_next to_new edge_for_vertex scanned_edges)
      lowcost_out edge_parent_out inf.
Proof.
  intros g s_next to_new wt_new scanned_edges
         eligible_vertex edge_for_vertex
         lowcost_in edge_parent_in lowcost_out edge_parent_out inf
         Hmatch Hscan.
  revert eligible_vertex edge_for_vertex Hmatch.
  induction Hscan as
    [lowcost edge_parent |
     de rest lowcost0 edge_parent0 lowcost1 edge_parent1
        lowcost2 edge_parent2 Hone Hrest IH].
  - intros eligible_vertex edge_for_vertex Hmatch _ _ _ _ _ _.
    exact Hmatch.
  - intros eligible_vertex edge_for_vertex Hmatch
           Hlow_range Hparent_range Htarget_graph Hde_range Hwt_inf Hweight.
    assert (Hmatch1 :
      lowcost_parent_match_by
        g eligible_vertex
        (add_scanned_edge_for_vertex g s_next to_new edge_for_vertex de)
        lowcost1 edge_parent1 inf).
    {
      eapply scan_one_directed_edge_update_lowcost_parent_match_by.
      - exact Hmatch.
      - exact Hone.
      - apply Htarget_graph. simpl; auto.
      - apply Hde_range. simpl; auto.
      - exact Hlow_range.
      - exact Hparent_range.
      - apply Hwt_inf. simpl; auto.
      - apply Hweight. simpl; auto.
    }
    destruct (scan_one_directed_edge_update_lengths
      g s_next to_new wt_new
      lowcost0 edge_parent0 de lowcost1 edge_parent1 Hone)
      as [Hlen_low Hlen_parent].
    eapply (IH eligible_vertex
      (add_scanned_edge_for_vertex g s_next to_new edge_for_vertex de)); eauto.
    + intros v Hv_graph.
      rewrite Hlen_low.
      apply Hlow_range; exact Hv_graph.
    + intros v Hv_graph.
      rewrite Hlen_parent.
      apply Hparent_range; exact Hv_graph.
    + intros de' Hde'.
      apply Htarget_graph. simpl; auto.
    + intros de' Hde'.
      apply Hde_range. simpl; auto.
    + intros de' Hde'.
      apply Hwt_inf. simpl; auto.
    + intros de' Hde'.
      apply Hweight. simpl; auto.
Qed.

Lemma scan_minIndex_adjacency_update_lowcost_parent_match_by :
  forall n m from to wt g s_next
         from_new first link to_new wt_new minIndex
         eligible_vertex edge_for_vertex
         lowcost_before edge_parent_before
         lowcost_after edge_parent_after inf,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    (forall e, 0 <= e < m -> Znth e wt 0 < inf) ->
    directed_array_graph g from_new to_new wt_new ->
    lowcost_parent_match_by
      g eligible_vertex edge_for_vertex
      lowcost_before edge_parent_before inf ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_before) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_before) ->
    scan_minIndex_adjacency_update
      g s_next from_new first link to_new wt_new minIndex
      lowcost_before edge_parent_before
      lowcost_after edge_parent_after ->
    lowcost_parent_match_by
      g eligible_vertex
      (add_vertex_directed_edges_for_vertex
        g s_next from_new to_new minIndex edge_for_vertex)
      lowcost_after edge_parent_after inf.
Proof.
  intros n m from to wt g s_next
         from_new first link to_new wt_new minIndex
         eligible_vertex edge_for_vertex
         lowcost_before edge_parent_before
         lowcost_after edge_parent_after inf
         Hgraph Hfrom_range Hto_range Hwt_range Hdir Hmatch
         Hlow_range Hparent_range Hscan.
  destruct Hscan as [scanned_edges [_ [Hperm Hscan]]].
  eapply lowcost_parent_match_by_iff.
  - eapply scan_directed_edges_update_lowcost_parent_match_by; eauto.
    + intros de Hde.
      eapply vertex_directed_edges_to_graph_vertex; eauto.
      eapply Permutation_in; [exact Hperm | exact Hde].
    + intros de Hde.
      eapply vertex_directed_edges_range.
      eapply Permutation_in; [exact Hperm | exact Hde].
    + intros de Hde.
      eapply vertex_directed_edges_weight_lt; eauto.
      eapply Permutation_in; [exact Hperm | exact Hde].
    + intros de Hde.
      eapply directed_array_graph_weight; eauto.
      eapply vertex_directed_edges_range.
      eapply Permutation_in; [exact Hperm | exact Hde].
  - intros v _ Heligible; exact Heligible.
  - intros v e _ _.
    apply add_scanned_edges_for_vertex_perm.
    exact Hperm.
Qed.

Lemma candidate_vertex_from_lowcost_lt_inf :
  forall (n m : Z) (from to wt : list Z)
         (g : G) (s : St) (lowcost edge_parent visited : list Z)
         (inf v : Z),
    array_graph n m from to wt g ->
    visited_matches_state g s visited ->
	    lowcost_parent_match g s lowcost edge_parent inf ->
	    0 <= v < n ->
	    Znth v visited 0 = 0 ->
	    Znth v lowcost 0 < inf ->
    candidate_vertex g s lowcost edge_parent inf v.
Proof.
  intros n m from to wt g s lowcost edge_parent visited inf v
         Hgraph Hvisited Hmatch Hv_range Hvisited0 Hlow_lt.
  assert (Hv_graph : In v (graph_vertices g)).
  { eapply array_graph_vertex_in; eauto. }
  assert (Hv_not_valid : ~ vvalid s.(Prim.graph_in_state) v).
  {
    intro Hv_valid.
    destruct (Hvisited v Hv_graph) as [_ Hvalid_to_visited].
    pose proof (Hvalid_to_visited Hv_valid) as Hvisited1.
    lia.
  }
	  unfold candidate_vertex.
	  split; [exact Hv_graph |].
	  split; [exact Hv_not_valid |].
  destruct Hmatch as [_ Hmatch].
	  specialize (Hmatch v Hv_graph Hv_not_valid).
  destruct Hmatch as [Hsome | Hnone].
  - destruct Hsome as [de [Hparent [Hde [Hlow [Hmin Hweight]]]]].
    unfold vertex_has_parent_edge.
    rewrite Hparent.
    split; [exact Hde |].
    split; [exact Hlow |].
    split; [exact Hmin | exact Hweight].
  - destruct Hnone as [_ [_ Hlow_eq]].
    lia.
Qed.

Lemma min_vertex_in_range_take_current :
  forall (n m j inf min minIndex : Z)
         (from to wt : list Z)
         (g : G) (s : St)
         (lowcost edge_parent visited : list Z),
    array_graph n m from to wt g ->
    visited_matches_state g s visited ->
    lowcost_parent_match g s lowcost edge_parent inf ->
	    min_vertex_in_range g s j inf minIndex lowcost edge_parent ->
	    0 <= j < n ->
		    Znth j visited 0 = 0 ->
		    Znth j lowcost 0 < min ->
	    (minIndex = -1 -> min = inf) ->
		    (minIndex <> -1 -> min = Znth minIndex lowcost 0) ->
    min_vertex_in_range g s (j + 1) inf j lowcost edge_parent.
Proof.
  intros n m j inf min minIndex from to wt g s
         lowcost edge_parent visited
         Hgraph Hvisited Hmatch Hmin_range Hj Hvisited0 Hlow_lt
         Hmin_none Hmin_some.
	  assert (Hlow_j_lt_inf : Znth j lowcost 0 < inf).
  {
    pose proof Hmin_range as Hmin_range_for_inf.
    destruct Hmin_range_for_inf as [[Hidx_none _] | [Hcand_idx [Hidx_in _]]].
    - rewrite (Hmin_none Hidx_none) in Hlow_lt; lia.
    - assert (Hidx_not_minus_one : minIndex <> -1).
      {
        rewrite <- In_Zrange in Hidx_in.
        lia.
      }
      destruct Hcand_idx as [_ [_ [_ [_ [Hlow_idx _]]]]].
      rewrite (Hmin_some Hidx_not_minus_one) in Hlow_lt.
      lia.
  }
  assert (Hcand_j :
    candidate_vertex g s lowcost edge_parent inf j).
  {
    eapply candidate_vertex_from_lowcost_lt_inf; eauto.
  }
  right.
  split; [exact Hcand_j |].
  split.
  - rewrite Zrange_0_snoc by lia.
    apply in_or_app; right; simpl; auto.
  - unfold min_object_of_subset.
    simpl.
    split.
    + split.
      * rewrite Zrange_0_snoc by lia.
        apply in_or_app; right; simpl; auto.
      * exact Hcand_j.
    + intros v [Hv_in Hcand_v].
      rewrite Zrange_0_snoc in Hv_in by lia.
      apply in_app_or in Hv_in.
      destruct Hv_in as [Hv_old | Hv_last].
      * pose proof Hmin_range as Hmin_range_old.
        destruct Hmin_range_old as [[_ Hnone_old] | [_ [Hidx_in Hmin_idx]]].
        -- exfalso; eapply Hnone_old; eauto.
        -- destruct Hmin_idx as [_ Hmin_idx_le].
           assert (Hidx_not_minus_one : minIndex <> -1).
           {
             rewrite <- In_Zrange in Hidx_in.
             lia.
           }
           specialize (Hmin_idx_le v ltac:(split; [exact Hv_old | exact Hcand_v])).
           rewrite (Hmin_some Hidx_not_minus_one) in Hlow_lt.
           simpl in Hmin_idx_le |- *.
           lia.
      * simpl in Hv_last.
        destruct Hv_last as [Hv_eq | []].
        subst v.
        simpl; lia.
Qed.

Lemma min_vertex_in_range_skip_visited :
  forall (n m j inf minIndex : Z)
         (from to wt : list Z)
         (g : G) (s : St)
         (lowcost edge_parent visited : list Z),
    array_graph n m from to wt g ->
	    visited_matches_state g s visited ->
	    min_vertex_in_range g s j inf minIndex lowcost edge_parent ->
	    0 <= j < n ->
		    Znth j visited 0 <> 0 ->
	    min_vertex_in_range g s (j + 1) inf minIndex lowcost edge_parent.
Proof.
  intros n m j inf minIndex from to wt g s lowcost edge_parent visited
         Hgraph Hvisited Hmin_range Hj Hvisited_nonzero.
  assert (Hj_graph : In j (graph_vertices g)).
  { eapply array_graph_vertex_in; eauto. }
  assert (Hj_valid : vvalid s.(Prim.graph_in_state) j).
  {
    destruct (Hvisited j Hj_graph) as [Hnonzero_to_valid _].
    apply Hnonzero_to_valid.
    exact Hvisited_nonzero.
  }
  assert (Hj_not_candidate :
    ~ candidate_vertex g s lowcost edge_parent inf j).
  {
    intros Hcand.
    destruct Hcand as [_ [Hj_not_valid _]].
    exact (Hj_not_valid Hj_valid).
  }
  destruct Hmin_range as [[Hidx_none Hnone] | [Hcand_idx [Hidx_in Hmin_idx]]].
  - left.
    split; [exact Hidx_none |].
    intros v Hv_in.
    rewrite Zrange_0_snoc in Hv_in by lia.
    apply in_app_or in Hv_in.
    destruct Hv_in as [Hv_old | Hv_last].
    + apply Hnone; exact Hv_old.
    + simpl in Hv_last.
      destruct Hv_last as [Hv_eq | []].
      subst v.
      exact Hj_not_candidate.
  - right.
    split; [exact Hcand_idx |].
    split.
    + rewrite Zrange_0_snoc by lia.
      apply in_or_app; left; exact Hidx_in.
    + unfold min_object_of_subset in *.
      destruct Hmin_idx as [Hidx_subset Hidx_min].
      split.
      * destruct Hidx_subset as [_ Hcand_minIndex].
        split.
        -- rewrite Zrange_0_snoc by lia.
           apply in_or_app; left; exact Hidx_in.
        -- exact Hcand_minIndex.
      * intros v [Hv_in Hcand_v].
        rewrite Zrange_0_snoc in Hv_in by lia.
        apply in_app_or in Hv_in.
        destruct Hv_in as [Hv_old | Hv_last].
        -- apply Hidx_min.
           split; [exact Hv_old | exact Hcand_v].
        -- simpl in Hv_last.
           destruct Hv_last as [Hv_eq | []].
           subst v.
           contradiction.
Qed.

Lemma min_vertex_in_range_skip_not_better :
  forall (n m j inf min minIndex : Z)
         (from to wt : list Z)
         (g : G) (s : St)
         (lowcost edge_parent visited : list Z),
    array_graph n m from to wt g ->
    visited_matches_state g s visited ->
    lowcost_parent_match g s lowcost edge_parent inf ->
	    min_vertex_in_range g s j inf minIndex lowcost edge_parent ->
	    0 <= j < n ->
		    Znth j visited 0 = 0 ->
		    Znth j lowcost 0 >= min ->
	    (minIndex = -1 -> min = inf) ->
		    (minIndex <> -1 -> min = Znth minIndex lowcost 0) ->
    min_vertex_in_range g s (j + 1) inf minIndex lowcost edge_parent.
Proof.
  intros n m j inf min minIndex from to wt g s
         lowcost edge_parent visited
         Hgraph Hvisited Hmatch Hmin_range Hj Hvisited0 Hlow_ge
         Hmin_none Hmin_some.
  destruct Hmin_range as [[Hidx_none Hnone] | [Hcand_idx [Hidx_in Hmin_idx]]].
  - left.
    split; [exact Hidx_none |].
    intros v Hv_in.
    rewrite Zrange_0_snoc in Hv_in by lia.
    apply in_app_or in Hv_in.
    destruct Hv_in as [Hv_old | Hv_last].
    + apply Hnone; exact Hv_old.
    + simpl in Hv_last.
      destruct Hv_last as [Hv_eq | []].
      subst v.
      intros Hcand_j.
      destruct Hcand_j as [_ [_ [_ [_ [Hlow_j _]]]]].
      rewrite (Hmin_none Hidx_none) in Hlow_ge.
      lia.
  - right.
    split; [exact Hcand_idx |].
    split.
    + rewrite Zrange_0_snoc by lia.
      apply in_or_app; left; exact Hidx_in.
    + unfold min_object_of_subset in *.
      destruct Hmin_idx as [Hidx_subset Hidx_min].
      split.
      * destruct Hidx_subset as [_ Hcand_minIndex].
        split.
        -- rewrite Zrange_0_snoc by lia.
           apply in_or_app; left; exact Hidx_in.
        -- exact Hcand_minIndex.
      * intros v [Hv_in Hcand_v].
        rewrite Zrange_0_snoc in Hv_in by lia.
        apply in_app_or in Hv_in.
        destruct Hv_in as [Hv_old | Hv_last].
        -- apply Hidx_min.
           split; [exact Hv_old | exact Hcand_v].
        -- simpl in Hv_last.
           destruct Hv_last as [Hv_eq | []].
           subst v.
           assert (Hidx_not_minus_one : minIndex <> -1).
           {
             rewrite <- In_Zrange in Hidx_in.
             lia.
           }
           rewrite (Hmin_some Hidx_not_minus_one) in Hlow_ge.
           simpl.
           lia.
Qed.

Definition selected_state_after_add
    (g : G) (src : V) (i n : Z)
    (s_before s_after : St)
    (from_new to_new edge_parent lowcost visited : list Z)
    (minIndex : V) : Prop :=
  (i = 0 /\
   minIndex = src /\
   initStPred g src s_after /\
   lowcost = replace_Znth src 0 (repeat 1000000000 (Z.to_nat n)) /\
   edge_parent = repeat (-1) (Z.to_nat n) /\
   visited = repeat 0 (Z.to_nat n) /\
   visited_matches_state g s_after (replace_Znth minIndex 1 visited)) \/
  (1 <= i < n /\
   growing_subgraph_state g s_before /\
   visited_matches_state g s_before visited /\
   lowcost_parent_match g s_before lowcost edge_parent 1000000000 /\
   selected_parent_edge_is_min_cut_edge g s_before edge_parent minIndex /\
   exists u v,
     selected_parent_pair g s_before from_new to_new edge_parent minIndex u v /\
     selected_parent_add_to_mst
       g s_before s_after from_new to_new edge_parent minIndex /\
     visited_matches_state g s_after (replace_Znth minIndex 1 visited)).

Lemma selected_state_after_add_visited :
  forall g src i n s_before s_after from_new to_new edge_parent lowcost visited minIndex,
    selected_state_after_add
      g src i n s_before s_after
      from_new to_new edge_parent lowcost visited minIndex ->
    visited_matches_state g s_after (replace_Znth minIndex 1 visited).
Proof.
  intros g src i n s_before s_after from_new to_new edge_parent lowcost visited minIndex H.
  destruct H as [[_ [_ [_ [_ [_ [_ Hvisited]]]]]]
               | [_ [_ [_ [_ [_ [u [v [_ [_ Hvisited]]]]]]]]]];
    exact Hvisited.
Qed.

Lemma selected_state_after_add_minIndex_vvalid :
  forall g src i n s_before s_after from_new to_new edge_parent lowcost visited minIndex,
    selected_state_after_add
      g src i n s_before s_after
      from_new to_new edge_parent lowcost visited minIndex ->
    vvalid s_after.(Prim.graph_in_state) minIndex.
Proof.
  intros g src i n s_before s_after from_new to_new edge_parent lowcost visited minIndex H.
  destruct H as [[_ [Hmin_src [Hinit _]]]
                | [_ [_ [_ [_ [_ Hex]]]]]].
  - unfold initStPred in Hinit.
    subst s_after.
    apply initSt_vvalid.
    exact Hmin_src.
  - destruct Hex as [u [v [_ [Hadd _]]]].
    eapply selected_parent_add_to_mst_minIndex_vvalid; eauto.
Qed.

Lemma selected_state_after_add_growing :
  forall n m from to wt g src i s_before s_after
         from_new to_new edge_parent lowcost visited minIndex,
    array_graph n m from to wt g ->
    In src (graph_vertices g) ->
    selected_state_after_add
      g src i n s_before s_after
      from_new to_new edge_parent lowcost visited minIndex ->
    growing_subgraph_state g s_after.
Proof.
  intros n m from to wt g src i s_before s_after
         from_new to_new edge_parent lowcost visited minIndex
         Hgraph Hsrc Hadd_state.
  destruct Hadd_state as [[_ [_ [Hinit _]]]
                         | [_ [Hgrowing [_ [_ [_ Hex]]]]]].
  - unfold initStPred in Hinit.
    subst s_after.
    eapply initSt_growing_subgraph_state; eauto.
  - destruct Hex as [u [v [_ [Hadd _]]]].
    eapply selected_parent_add_to_mst_growing; eauto.
Qed.

Lemma scan_minIndex_adjacency_update_lowcost_parent_match :
  forall n m from to wt g s_before s_after
         from_new first link to_new wt_new
         lowcost_before edge_parent_before
         lowcost_after edge_parent_after visited src i minIndex,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
	    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
	    (forall e, 0 <= e < m -> Znth e wt 0 < 1000000000) ->
		    directed_array_graph g from_new to_new wt_new ->
		    In src (graph_vertices g) ->
		    selected_state_after_add
		      g src i n s_before s_after
	      from_new to_new edge_parent_before lowcost_before visited minIndex ->
    scan_minIndex_adjacency_update
      g s_after from_new first link to_new wt_new minIndex
      lowcost_before edge_parent_before
      lowcost_after edge_parent_after ->
    lowcost_parent_match g s_after lowcost_after edge_parent_after 1000000000.
Proof.
  intros n m from to wt g s_before s_after
         from_new first link to_new wt_new
	         lowcost_before edge_parent_before
	         lowcost_after edge_parent_after visited src i minIndex
	         Hgraph Hfrom_range Hto_range Hwt_range Hdir Hsrc
	         Hstate Hscan.
	  destruct Hstate as
	    [[Hi [Hmin_src [Hinit [Hlow_init [Hparent_init [_ _]]]]]]
	    | [Hi [_ [_ [Hmatch_before [_ Hex]]]]]].
	  - subst minIndex lowcost_before edge_parent_before.
	    unfold initStPred in Hinit.
	    subst s_after.
    assert (Hinit_match_by :
      lowcost_parent_match_by
        g
        (fun v => ~ vvalid (Prim.graph_in_state (initSt g src)) v)
        (fun _ _ => False)
        (replace_Znth src 0 (repeat 1000000000 (Z.to_nat n)))
        (repeat (-1) (Z.to_nat n))
        1000000000).
    { eapply init_lowcost_parent_match_by_empty; eauto. }
    destruct Hinit_match_by as [Hinit_range Hinit_body].
		    apply lowcost_parent_match_by_to.
		    eapply lowcost_parent_match_by_iff.
	    + eapply scan_minIndex_adjacency_update_lowcost_parent_match_by
	        with
	          (eligible_vertex :=
	             fun v => ~ vvalid (Prim.graph_in_state (initSt g src)) v)
	          (edge_for_vertex := fun _ _ => False)
	          (lowcost_before :=
	             replace_Znth src 0 (repeat 1000000000 (Z.to_nat n)))
	          (edge_parent_before := repeat (-1) (Z.to_nat n)).
	      * exact Hgraph.
	      * exact Hfrom_range.
		      * exact Hto_range.
		      * exact Hwt_range.
		      * exact Hdir.
		      * split; [exact Hinit_range | exact Hinit_body].
		      * intros v Hv; destruct (Hinit_range v Hv) as [Hlow _]; exact Hlow.
		      * intros v Hv; destruct (Hinit_range v Hv) as [_ Hparent]; exact Hparent.
		      * exact Hscan.
	    + intros v _ Helig; exact Helig.
	    + intros v e _ Helig.
		      eapply initSt_cut_edges_match
		        with (n := n) (m := m) (from := from) (to := to)
		             (wt := wt) (wt_new := wt_new); eauto.
	  - destruct Hex as [u [v [_ [Hadd _]]]].
    pose proof (lowcost_parent_match_to_by
      g s_before lowcost_before edge_parent_before 1000000000
      Hmatch_before) as Hmatch_before_by.
    destruct Hmatch_before_by as [Hbefore_range Hbefore_body].
		    apply lowcost_parent_match_by_to.
		    eapply lowcost_parent_match_by_iff.
	    + eapply scan_minIndex_adjacency_update_lowcost_parent_match_by
	        with
	          (eligible_vertex :=
	             fun v => ~ vvalid (Prim.graph_in_state s_before) v)
	          (edge_for_vertex := fun v e => is_cut_edge_to_vertex g s_before v e)
	          (lowcost_before := lowcost_before)
	          (edge_parent_before := edge_parent_before);
	        [ exact Hgraph
	        | exact Hfrom_range
		        | exact Hto_range
		        | exact Hwt_range
		        | exact Hdir
		        | split; [exact Hbefore_range | exact Hbefore_body]
		        | intros v0 Hv0; destruct (Hbefore_range v0 Hv0) as [Hlow _]; exact Hlow
		        | intros v0 Hv0; destruct (Hbefore_range v0 Hv0) as [_ Hparent]; exact Hparent
		        | exact Hscan ].
    + intros v0 _ Helig Hv_old.
      apply Helig.
      eapply selected_parent_add_to_mst_old_vvalid; eauto.
    + intros v0 e _ Helig.
	      apply selected_parent_add_to_mst_cut_edges_match
	        with (n := n) (m := m) (from := from) (to := to) (wt := wt)
	             (wt_new := wt_new)
	             (edge_parent := edge_parent_before); auto.
Qed.

Lemma array_graph_bijective_vertex_count :
  forall n m from to wt g,
    gvalid g ->
    array_graph n m from to wt g ->
    Zlength (bijective_listV g) = n.
Proof.
  intros n m from to wt g Hg Hgraph.
  pose proof (array_graph_vertex_count _ _ _ _ _ _ Hgraph) as Hlen_vertices.
  assert (Hperm : Permutation (bijective_listV g) (graph_vertices g)).
  {
    apply NoDup_Permutation.
    - apply bijective_listV_NoDup; auto.
    - unfold array_graph in Hgraph.
      destruct Hgraph as [Hvertices _].
      rewrite Hvertices.
      apply NoDup_Zrange.
    - intros v.
      rewrite bijective_vertices by auto.
      unfold vvalid, graph_instance.
      reflexivity.
  }
  apply Permutation_length in Hperm.
  rewrite !Zlength_correct in *.
  lia.
Qed.

Lemma selected_parent_Prim_body_rel :
  forall g s s_next from_new to_new edge_parent minIndex,
    selected_parent_edge_is_min_cut_edge g s edge_parent minIndex ->
    selected_parent_add_to_mst g s s_next from_new to_new edge_parent minIndex ->
    @Prim.Prim_body G V E graph_instance g edge_weight_instance s tt s_next.
Proof.
  intros g s s_next from_new to_new edge_parent minIndex Hmin Hadd.
  destruct Hadd as [u [v [Hpair Hadd]]].
  destruct Hpair as [_ Hpair_core].
  unfold Prim.Prim_body, Prim.get_min_cut_edge, Prim.add_to_mst.
  unfold StateRelMonad.bind, get, update.
  exists (Znth minIndex edge_parent 0 / 2), s.
  split; [split; [exact Hmin | reflexivity] |].
  exists (u, v), s.
  split; [split; [exact Hpair_core | reflexivity] |].
  exact Hadd.
Qed.

Lemma selected_parent_prim2_loop_step :
  forall n m from to wt g i X s s_next from_new to_new edge_parent minIndex,
    gvalid g ->
    array_graph n m from to wt g ->
    1 <= i ->
    i < n ->
    safeExec (prim_state_is s) (Prim2_loop g (i - 1)) X ->
    selected_parent_edge_is_min_cut_edge g s edge_parent minIndex ->
    selected_parent_add_to_mst g s s_next from_new to_new edge_parent minIndex ->
    safeExec (prim_state_is s_next) (Prim2_loop g i) X.
Proof.
  intros n m from to wt g i X s s_next from_new to_new edge_parent minIndex
         Hg Hgraph Hi_low Hi_high Hsafe Hmin Hadd.
  assert (Hhi : Zlength (bijective_listV g) = n).
  { eapply array_graph_bijective_vertex_count; eauto. }
  unfold Prim2_loop in *.
  change (@range_iter St unit (i - 1) (Zlength (bijective_listV g) - 1)
            (fun _ _ => @Prim.Prim_body G V E graph_instance g edge_weight_instance) tt)
    with ((fun '(lo, a) =>
             @range_iter St unit lo (Zlength (bijective_listV g) - 1)
               (fun _ _ => @Prim.Prim_body G V E graph_instance g edge_weight_instance) a)
            (i - 1, tt)) in Hsafe.
  pose proof (@range_iter_unfold_aux St unit
                (Zlength (bijective_listV g) - 1)
                (fun _ _ => @Prim.Prim_body G V E graph_instance g edge_weight_instance))
    as Hrange.
  specialize (Hrange (i - 1, tt)).
  eapply safeExec_proequiv in Hsafe; [| exact Hrange].
  simpl in Hsafe.
  apply safeExec_choice_l in Hsafe.
  apply safeExec_test_bind in Hsafe.
  2: { rewrite Hhi; lia. }
  simpl in Hsafe.
  unfold safeExec, safe in *.
  destruct Hsafe as [st [Hst Hwp]].
  unfold prim_state_is in Hst; subst st.
  exists s_next.
  split; [unfold prim_state_is; reflexivity|].
  replace (i - 1 + 1) with i in * by lia.
  unfold weakestpre in Hwp.
  unfold weakestpre.
  intros r st Htail.
  apply Hwp.
  unfold StateRelMonad.bind.
  exists tt, s_next.
  split; [| exact Htail].
  eapply selected_parent_Prim_body_rel; eauto.
Qed.

Lemma Prim2_loop_finish :
  forall n m from to wt g i X s,
    gvalid g ->
    array_graph n m from to wt g ->
    i >= n ->
    i <= n ->
    safeExec (prim_state_is s) (Prim2_loop g (i - 1)) X ->
    safeExec (prim_state_is s) (return tt) X.
Proof.
  intros n m from to wt g i X s Hg Hgraph Hi_ge Hi_le Hsafe.
  assert (Hhi : Zlength (bijective_listV g) = n).
  { eapply array_graph_bijective_vertex_count; eauto. }
  unfold Prim2_loop in *.
  change (@range_iter St unit (i - 1) (Zlength (bijective_listV g) - 1)
            (fun _ _ => @Prim.Prim_body G V E graph_instance g edge_weight_instance) tt)
    with ((fun '(lo, a) =>
             @range_iter St unit lo (Zlength (bijective_listV g) - 1)
               (fun _ _ => @Prim.Prim_body G V E graph_instance g edge_weight_instance) a)
            (i - 1, tt)) in Hsafe.
  pose proof (@range_iter_unfold_aux St unit
                (Zlength (bijective_listV g) - 1)
                (fun _ _ => @Prim.Prim_body G V E graph_instance g edge_weight_instance))
    as Hrange.
  specialize (Hrange (i - 1, tt)).
  eapply safeExec_proequiv in Hsafe; [| exact Hrange].
  simpl in Hsafe.
  apply safeExec_choice_r in Hsafe.
  apply safeExec_test_bind in Hsafe.
  2: { rewrite Hhi; lia. }
  simpl in Hsafe.
  exact Hsafe.
Qed.

Lemma cut_edges_covered_by_candidates :
  forall (n m : Z) (from to wt : list Z) (g : G) (s : St)
         (lowcost edge_parent : list Z) (inf : Z),
    array_graph n m from to wt g ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    forall e,
      Prim.is_cut_edge g s e ->
      exists v,
        In v (Zrange 0 n) /\
        candidate_vertex g s lowcost edge_parent inf v /\
        is_cut_edge_to_vertex g s v e.
Proof.
  intros n m from to wt g s lowcost edge_parent inf Hgraph Hmatch e Hcut.
  destruct Hgraph as [Hvertices _].
  destruct Hcut as [u [v [Hu [Hnot_v Hstep]]]].
  exists v.
  assert (Hv_graph : In v (graph_vertices g)).
  {
    pose proof (step_vvalid2 g e u v Hstep) as Hv.
    cbn in Hv.
    exact Hv.
  }
  assert (Hv_range : In v (Zrange 0 n)).
  { rewrite <- Hvertices; exact Hv_graph. }
  split; [exact Hv_range |].
  assert (Hendpoint_v : edge_src g e = v \/ edge_dst g e = v).
  {
    unfold graph_step in Hstep.
    destruct Hstep as [_ [_ [[_ ->] | [_ ->]]]]; auto.
  }
  assert (Hcut_to_v : is_cut_edge_to_vertex g s v e).
  {
    split; [exact Hnot_v |].
    split; [exact Hendpoint_v |].
    exists u, v.
    split; [exact Hu |].
    split; [exact Hnot_v | exact Hstep].
  }
	  split; [| exact Hcut_to_v].
	  unfold candidate_vertex.
	  split; [exact Hv_graph |].
	  split; [exact Hnot_v |].
  destruct Hmatch as [_ Hmatch].
	  specialize (Hmatch v Hv_graph Hnot_v).
  destruct Hmatch as [[de [Hparent [Hde [Hlow [Hmin Hweight]]]]] | [Hnone _]].
  - unfold vertex_has_parent_edge.
    rewrite Hparent.
    split; [exact Hde |].
    split; [exact Hlow |].
    split; [exact Hmin | exact Hweight].
      - exfalso.
        exact (Hnone e Hcut_to_v).
Qed.

Lemma cut_edge_exists_candidate_vertex_exists_in_range :
  forall (n m : Z) (from to wt : list Z) (g : G) (s : St)
         (lowcost edge_parent : list Z) (inf : Z),
    array_graph n m from to wt g ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    (exists e, Prim.is_cut_edge g s e) ->
    candidate_vertex_exists_in_range n g s lowcost edge_parent inf.
Proof.
  intros n m from to wt g s lowcost edge_parent inf
         Hgraph Hmatch [e Hcut].
  pose proof (cut_edges_covered_by_candidates
    n m from to wt g s lowcost edge_parent inf Hgraph Hmatch e Hcut)
    as [v [Hv_range [Hcand _]]].
  exists v.
  split; [exact Hv_range | exact Hcand].
Qed.

Lemma unfinished_connected_state_has_candidate_vertex_by_count :
  forall (n m : Z) (from to wt : list Z) (g : G) (s : St)
         (lowcost edge_parent : list Z) (inf : Z),
    array_graph n m from to wt g ->
    connected g ->
    growing_subgraph_state g s ->
    (exists x, vvalid s.(Prim.graph_in_state) x) ->
    state_vertex_count s < n ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    candidate_vertex_exists_in_range n g s lowcost edge_parent inf.
Proof.
  intros n m from to wt g s lowcost edge_parent inf
         Hgraph Hconn Hgrow Hnonempty Hlt Hmatch.
  eapply cut_edge_exists_candidate_vertex_exists_in_range; eauto.
  eapply has_cut_edge_exists_by_state_vertex_count; eauto.
Qed.

Lemma min_vertex_parent_is_min_cut_edge :
  forall (g : G) (s : St) (lowcost edge_parent : list Z)
         (n m inf : Z) (from to wt : list Z) (minIndex : V),
    array_graph n m from to wt g ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    min_vertex_in_range g s n inf minIndex lowcost edge_parent ->
    minIndex <> -1 ->
    selected_parent_edge_is_min_cut_edge g s edge_parent minIndex.
Proof.
  intros g s lowcost edge_parent n m inf from to wt minIndex
    Hgraph Hmatch Hloop HminIndex.
  pose proof (cut_edges_covered_by_candidates
    n m from to wt g s lowcost edge_parent inf Hgraph Hmatch) as Hcut_cover.
  destruct Hloop as [Hnone | Hsome].
  - destruct Hnone as [HminIndex_eq _].
    contradiction.
  - destruct Hsome as
      [Hcand_minIndex [Hrange_minIndex Hmin_vertex]].
    destruct Hcand_minIndex as [_ [_ Hparent_minIndex]].
    destruct Hparent_minIndex as
      [_ [_ [_ [Hmin_edge_to_minIndex Hweight_minIndex]]]].
    destruct Hmin_edge_to_minIndex as
      [Hcut_to_minIndex _].
    destruct Hmin_vertex as [_ Hmin_vertex].
    unfold selected_parent_edge_is_min_cut_edge.
    split.
    + destruct Hcut_to_minIndex as [_ [_ Hcut]].
      exact Hcut.
    + intros e Hcut_e.
      destruct (Hcut_cover e Hcut_e) as
        [v [Hrange_v [Hcand_v Hcut_to_v_e]]].
      assert (Hin_candidate :
        In v (Zrange 0 n) /\
        candidate_vertex g s lowcost edge_parent inf v)
        by (split; [exact Hrange_v | exact Hcand_v]).
      destruct Hcand_v as [_ [_ Hparent_v]].
      destruct Hparent_v as [_ [_ [_ [Hmin_edge_to_v Hweight_v]]]].
      destruct Hmin_edge_to_v as [_ Hmin_edge_to_v].
	      eapply Z_op_le_trans with (y := Some (Znth v lowcost 0)).
	      * replace (weight g (Znth minIndex edge_parent 0 / 2))
	          with (Some (Znth minIndex lowcost 0)) by (symmetry; exact Hweight_minIndex).
	        exact (Hmin_vertex v Hin_candidate).
	      * replace (Some (Znth v lowcost 0))
	          with (weight g (Znth v edge_parent 0 / 2)) by exact Hweight_v.
	        apply Hmin_edge_to_v.
	        exact Hcut_to_v_e.
Qed.
      

Definition prim_result_graph_matches_array
    (n: Z) (rf rt rw: list Z) (g rg : G) : Prop :=
  0 <= n /\
  (forall v, In v (Zrange 0 n) -> vvalid rg v) /\
  Zlength rf = n - 1 /\
  Zlength rt = n - 1 /\
  Zlength rw = n - 1 /\
  (forall i, In i (Zrange 0 (n - 1)) ->
    exists e,
      evalid rg e /\
      step_aux rg e (Znth i rf 0) (Znth i rt 0) /\
      weight g e = Some (Znth i rw 0)) /\
  (forall e,
    evalid rg e ->
    exists i,
      In i (Zrange 0 (n - 1)) /\
      step_aux rg e (Znth i rf 0) (Znth i rt 0) /\
      weight g e = Some (Znth i rw 0)).

(** 返回数组前缀的循环不变量。
    中间阶段不只记录长度，还记录第 k 个输出槽位对应点 k+1 的 parent 边。
    由于输出循环按 i = 1,2,... 扫描，前缀 idx 正好对应顶点 1..idx。 *)
Definition prim_result_graph_matches_array_prefix
    (n idx : Z) (rf rt rw : list Z) (g rg : G)
    (edge_parent from_new to_new wt_new : list Z) : Prop :=
  0 <= idx <= n - 1 /\
  Zlength rf = idx /\
  Zlength rt = idx /\
  Zlength rw = idx /\
  (forall k,
    In k (Zrange 0 idx) ->
    let de := Znth (k + 1) edge_parent 0 in
    let e := de / 2 in
    evalid rg e /\
    step_aux rg e (Znth k rf 0) (Znth k rt 0) /\
    weight g e = Some (Znth k rw 0) /\
    Znth k rf 0 = Znth de from_new 0 /\
    Znth k rt 0 = Znth de to_new 0 /\
    Znth k rw 0 = Znth de wt_new 0).

Lemma prim_result_graph_matches_array_of_full_prefix :
  forall n m from to wt g src s rg rf rt rw edge_parent from_new to_new wt_new,
    array_graph n m from to wt g ->
    src = 0 ->
    growing_subgraph_state g s ->
    state_vertex_count s = n ->
    parent_edges_match_state g src s edge_parent ->
    prim_state_graph_matches rg s ->
    prim_result_graph_matches_array_prefix
      n (n - 1) rf rt rw g rg edge_parent from_new to_new wt_new ->
    prim_result_graph_matches_array n rf rt rw g rg.
Proof.
  intros n m from to wt g src s rg rf rt rw
         edge_parent from_new to_new wt_new
         Hgraph Hsrc Hgrow Hcount Hparent Hmatch Hprefix.
  unfold prim_result_graph_matches_array_prefix in Hprefix.
  destruct Hprefix as [Hidx [Hlen_rf [Hlen_rt [Hlen_rw Hslots]]]].
  unfold prim_result_graph_matches_array.
  unfold prim_state_graph_matches in Hmatch.
  subst rg.
  split; [lia|].
  split.
  - intros v Hv.
    apply completed_growing_subgraph_vvalid with (n := n) (m := m)
      (from := from) (to := to) (wt := wt) (g := g); auto.
    destruct Hgraph as [Hverts _].
    rewrite Hverts.
    exact Hv.
  - split; [exact Hlen_rf|].
    split; [exact Hlen_rt|].
    split; [exact Hlen_rw|].
    split.
    + intros i Hi.
      specialize (Hslots i Hi).
      destruct Hslots as [He [Hs [Hw _]]].
      exists (Znth (i + 1) edge_parent 0 / 2).
      split; [exact He|].
      split; [exact Hs|].
      exact Hw.
    + intros e He.
      destruct Hparent as [_ [_ Hparent_exact]].
      apply Hparent_exact in He.
      destruct He as [v [Hv_in [Hv_not_src [Hv_valid Heq]]]].
      subst e.
      assert (Hv_range : 0 <= v < n).
      { eapply array_graph_vertex_range; eauto. }
      assert (Hi_range : In (v - 1) (Zrange 0 (n - 1))).
      {
        apply In_Zrange.
        subst src.
        lia.
      }
      specialize (Hslots (v - 1) Hi_range).
      replace (v - 1 + 1) with v in Hslots by lia.
      destruct Hslots as [_ [Hs [Hw _]]].
      exists (v - 1).
      split; [exact Hi_range|].
      split; [exact Hs|].
      exact Hw.
Qed.
