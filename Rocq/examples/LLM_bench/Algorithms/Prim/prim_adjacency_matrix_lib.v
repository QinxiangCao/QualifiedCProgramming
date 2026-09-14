Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import IntLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.Zweight.
Require Import GraphLib.subgraph.subgraph.
From GraphLib.undirected Require Import tree.
From GraphLib.examples Require Import prim.
From ListLib Require Import Base.Positional.
From SumLib Require Import ZRange.
From MaxMinLib Require Import MaxMin Interface.
From MonadLib.StateRelMonad Require Export StateRelBasic.
From MonadLib.StateRelMonad Require Import StateRelHoare FixpointLib safeexec_lib.
Require Algorithms.Prim.Prim.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.epath.
Import ListNotations.
Import MonadNotation.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Definition V : Type := Z.


Definition E : Type := (V * V)%type.

Definition E_eq_dec : forall e1 e2 : E, {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality; apply Z.eq_dec.
Defined.

Definition edge_connects (e : E) (u v : V) : Prop :=
  (fst e = u /\ snd e = v) \/
  (fst e = v /\ snd e = u).

(** [undirected_edge u v] 是由两个端点确定的无向边表示。
    为了让[(u,v)]和[(v,u)]表示同一条边，这里总是把较小端点放在前面。 *)
Definition undirected_edge (u v : V) : E :=
  if Z.leb u v then (u, v) else (v, u).

Lemma undirected_edge_comm :
  forall u v, undirected_edge u v = undirected_edge v u.
Proof.
  intros u v.
  unfold undirected_edge.
  destruct (Z.leb_spec0 u v);
    destruct (Z.leb_spec0 v u); try lia; try reflexivity.
  assert (u = v) by lia.
  subst.
  reflexivity.
Qed.

Lemma undirected_edge_connects :
  forall u v, edge_connects (undirected_edge u v) u v.
Proof.
  intros u v.
  unfold undirected_edge.
  destruct (Z.leb_spec0 u v); simpl.
  - left; auto.
  - right; auto.
Qed.

Lemma undirected_edge_idempotent :
  forall u v,
    undirected_edge (fst (undirected_edge u v)) (snd (undirected_edge u v)) =
    undirected_edge u v.
Proof.
  intros u v.
  unfold undirected_edge.
  destruct (Z.leb_spec0 u v); simpl.
  - destruct (Z.leb_spec0 u v); lia || reflexivity.
  - destruct (Z.leb_spec0 v u); lia || reflexivity.
Qed.

Lemma undirected_edge_eq_cases :
  forall u v p i,
    undirected_edge u v = undirected_edge p i ->
    (u = p /\ v = i) \/ (u = i /\ v = p).
Proof.
  intros u v p i Heq.
  unfold undirected_edge in Heq.
  destruct (Z.leb_spec0 u v);
    destruct (Z.leb_spec0 p i);
    inversion Heq; subst; auto.
Qed.



Record G : Type := mkG {
  graph_weight : E -> Z;
  graph_vertices : list V;
  graph_edges : list E;
}.

Definition default_edge : E := (-1, -1).

Definition default_edge_list (n : Z) : list E :=
  repeat default_edge (Z.to_nat n).

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

Lemma Znth_replace_Znth_same_any :
  forall {A : Type} (l : list A) i (v d : A),
    0 <= i < Zlength l ->
    Znth i (replace_Znth i v l) d = v.
Proof.
  intros A l i v d Hi.
  unfold Znth.
  apply Znth_replace_Znth_Same.
  exact Hi.
Qed.

Lemma Znth_replace_Znth_diff_any :
  forall {A : Type} (l : list A) i j (v d : A),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    i <> j ->
    Znth j (replace_Znth i v l) d = Znth j l d.
Proof.
  intros A l i j v d Hi Hj Hneq.
  unfold Znth.
  apply Znth_replace_Znth_Diff; auto.
Qed.

Lemma int_array_missing_store_merge_to_full :
  forall p i n a l,
    0 <= i < n ->
    (IntArray.missing_i p i 0 n l **
     ((p + i * sizeof (INT)) # Int |-> a))
    |-- IntArray.full p n (replace_Znth i a l).
Proof.
  intros p i n a l Hi.
  sep_apply (derivable1_sepcon_comm
    (IntArray.missing_i p i 0 n l)
    ((p + i * sizeof (INT)) # Int |-> a)).
  sep_apply (IntArray.missing_i_merge_to_full p i n a l); auto.
  cancel.
Qed.

Lemma int_ptr_array2_missing_store_row_merge_to_full :
  forall x i n row_ptr rows row,
    0 <= i < n ->
    (IntPtrArray2.missing_i x n i row_ptr rows **
     ((x + i * sizeof (PTR)) # Ptr |-> row_ptr) **
     IntArray.full row_ptr (Zlength row) row)
    |-- IntPtrArray2.full x n (replace_Znth i row rows).
Proof.
  intros x i n row_ptr rows row Hi.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    x i n row_ptr rows row Hi) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (sizeof (PTR)) with ptr_size_Z in Hmerge.
  change (IntPtrArray2.ElemArray.full row_ptr (Zlength row) row)
    with (IntArray.full row_ptr (Zlength row) row) in Hmerge.
  change (sizeof (PTR)) with ptr_size_Z.
  sep_apply (derivable1_sepcon_comm
    (IntPtrArray2.missing_i x n i row_ptr rows **
     ((x + i * ptr_size_Z) # Ptr |-> row_ptr))
    (IntArray.full row_ptr (Zlength row) row)).
  sep_apply (derivable1_sepcon_comm
    (IntArray.full row_ptr (Zlength row) row **
     IntPtrArray2.missing_i x n i row_ptr rows)
    ((x + i * ptr_size_Z) # Ptr |-> row_ptr)).
  sep_apply Hmerge.
  cancel.
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

Definition edge_src (g : G) (e : E) : V :=
  fst e.

Definition edge_dst (g : G) (e : E) : V :=
  snd e.

Definition edge_endpoints_valid (g : G) (e : E) : Prop :=
  In (edge_src g e) (graph_vertices g) /\
  In (edge_dst g e) (graph_vertices g).

(** * GraphLib 图接口
 *)

Definition graph_step (g : G) (e : E) (x y : V) : Prop :=
  In e (graph_edges g) /\
  edge_endpoints_valid g e /\
  ((x = edge_src g e /\ y = edge_dst g e) \/
   (x = edge_dst g e /\ y = edge_src g e)).

Definition graph_wf (g : G) : Prop :=
  forall e, In e (graph_edges g) -> exists u v, graph_step g e u v.



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
    destruct Hstep as [_ [[Hu Hv] Hxy]].
    destruct Hxy as [[-> _] | [-> _]]; auto.
  - intros g e x y Hstep.
    destruct Hstep as [_ [[Hu Hv] Hxy]].
    destruct Hxy as [[_ ->] | [_ ->]]; auto.
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
  destruct Hstep as [He [[Hu Hv] Hxy]].
  repeat split; auto.
  destruct Hxy as [[-> ->] | [-> ->]]; auto.
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
  nodup E_eq_dec (graph_edges g).

#[export] Instance elist_bijective_instance : EListBijective G V E.
Proof.
  refine {| bijective_listE := valid_edges |}.
  - intros g Hg.
    unfold valid_edges.
    apply NoDup_nodup.
  - intros g _ e.
    unfold valid_edges.
    rewrite nodup_In.
    split; auto.
Qed.
#[export] Instance edge_weight_instance : EdgeWeight G E := {|
  weight := fun g e => Some (graph_weight g e);
|}.

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

(** * Prim 状态接口

    
 *)

Definition St : Type := @Prim.St G.

Definition empty_graph_of (g : G) (src : V) : G :=
  mkG (graph_weight g) (src :: nil) nil.

Lemma empty_graph_valid_of :
  forall g src, gvalid (empty_graph_of g src).
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
  - intros e. simpl. split; intros H.
    + destruct H.
    + contradiction.
Defined.

Definition initSt (g : G) (src : V) : St :=
  @Prim.initSt G V E graph_instance gvalid_instance src
    (emptyGraph_instance g src).

Definition initStPred (g : G) (src : V) : St -> Prop :=
  fun s => s = initSt g src.

Record PrimEnv (g : G) (src : V) : Prop := mkPrimEnv {
  prim_graph_valid : gvalid g;
  prim_src_valid : vvalid g src;
  prim_connected : connected g;
}.

Definition state_vertex_count (s : St) : Z :=
  vertex_num s.(Prim.graph_in_state).

Lemma state_vertex_count_positive_exists :
  forall s,
    gvalid s.(Prim.graph_in_state) ->
    0 < state_vertex_count s ->
    exists x, vvalid s.(Prim.graph_in_state) x.
Proof.
  intros s Hvalid Hpos.
  unfold state_vertex_count, vertex_num in Hpos.
  destruct (bijective_listV s.(Prim.graph_in_state)) as [| x xs] eqn:Hlist.
  - rewrite Zlength_correct in Hpos.
    simpl in Hpos. lia.
  - exists x.
    apply (proj1 (bijective_vertices s.(Prim.graph_in_state) Hvalid x)).
    rewrite Hlist. simpl. auto.
Qed.

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

Definition prim_state_is (s0 : St) : St -> Prop :=
  fun s => s = s0.

Definition prim_state_graph_matches (g : G) : St -> Prop :=
  fun s => s.(Prim.graph_in_state) = g.

Definition return_is_mst (g rg : G) : Prop :=
  is_mst g rg.

Definition growing_subgraph_state (g : G) (s : St) : Prop :=
  gvalid s.(Prim.graph_in_state) /\
  connected s.(Prim.graph_in_state) /\
  subgraph2 s.(Prim.graph_in_state) g /\
  (forall e, graph_weight s.(Prim.graph_in_state) e = graph_weight g e).

Lemma initSt_growing_subgraph_state :
  forall g src,
    PrimEnv g src ->
    growing_subgraph_state g (initSt g src).
Proof.
  intros g src Henv.
  split.
  - apply empty_graph_valid_of.
  - split.
    + intros x y Hx Hy.
      apply initSt_vvalid in Hx.
      apply initSt_vvalid in Hy.
      subst.
      unfold reachable.
      reflexivity.
    + split.
      * constructor.
        -- intros x Hx.
           apply initSt_vvalid in Hx.
           subst.
           apply prim_src_valid.
           exact Henv.
        -- intros x y e Hstep.
           unfold initSt in Hstep.
           simpl in Hstep.
           unfold empty_graph_of, step_aux, graph_instance, graph_step in Hstep.
           simpl in Hstep.
           destruct Hstep as [He _].
           contradiction.
      * intros e. reflexivity.
Qed.

Definition visited_matches_state (g : G) (s : St) (visited : list Z) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    (Znth v visited 0 <> 0 <-> vvalid s.(Prim.graph_in_state) v).

(** ** ghost语义里维护一个叫edge_parent的list E 

    邻接矩阵版 C 程序不要求维护 edge_parent ；但是证明里仍维护一个 ghost的
    edge_parent来说明：
    - 每个已经加入生长图、且不是源点的顶点，都有一条合法 parent 边；
    - 当前生长图里的边，正好就是这些 parent 边。
    方便e <- get_min_cut_edge is_cut_edge这步。
 *)
Definition selected_edges_range_state
    (g : G) (src : V) (s : St) (edge_parent : list E) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    v <> src ->
    vvalid s.(Prim.graph_in_state) v ->
    In (Znth v edge_parent default_edge) (graph_edges g).

Definition selected_edges_exact_state
    (g : G) (src : V) (s : St) (edge_parent : list E) : Prop :=
  forall e,
    evalid s.(Prim.graph_in_state) e <->
    exists v,
      In v (graph_vertices g) /\
      v <> src /\
      vvalid s.(Prim.graph_in_state) v /\
      e = Znth v edge_parent default_edge.

Definition selected_edges_match_state
    (g : G) (src : V) (s : St) (edge_parent : list E) : Prop :=
  vvalid s.(Prim.graph_in_state) src /\
  selected_edges_range_state g src s edge_parent /\
  selected_edges_exact_state g src s edge_parent.

(** ** C层父点数组和ghost父边列表的桥接

    返回MST邻接矩阵的C程序会真实维护一个[vertex_parent]数组：
    [vertex_parent[v] = p]表示点[v]通过父点[p]连入MST。

    但抽象Prim证明仍沿用ghost的[edge_parent : list E]：
    [edge_parent[v]]表示点[v]连入MST所用的规范无向边。
/
 *)
Definition vertex_parent_matches_edge_parent
    (g : G) (src : V) (vertex_parent : list Z) (edge_parent : list E) : Prop :=
  forall v,
    In v (graph_vertices g) ->
    0 <= v < Zlength vertex_parent /\
    0 <= v < Zlength edge_parent /\
    let p := Znth v vertex_parent (-1) in
    let e := Znth v edge_parent default_edge in
    (v = src -> p = -1 /\ e = default_edge) /\
    ((p = -1 /\ e = default_edge) \/
     (p <> -1 /\
      In p (graph_vertices g) /\
      p <> v /\
      e = undirected_edge p v /\
      graph_step g e p v)).

Lemma initSt_selected_edges_match_state :
  forall g src edge_parent,
    selected_edges_match_state g src (initSt g src) edge_parent.
Proof.
  intros g src edge_parent.
  unfold selected_edges_match_state.
  split.
  - rewrite initSt_vvalid. reflexivity.
  - split.
    + intros v _ Hv_src Hv_valid.
      rewrite initSt_vvalid in Hv_valid.
      contradiction.
    + intros e.
      split.
      * intros He.
        unfold initSt in He.
        simpl in He.
        unfold graph_instance in He.
        simpl in He.
        contradiction.
      * intros [v [_ [Hv_src [Hv_valid _]]]].
        rewrite initSt_vvalid in Hv_valid.
        contradiction.
Qed.

(** ** 加边操作

    [E] 是点对，所以边的端点由边本身决定。加边时不再“修改边编号
    的解释”，只是把这条边加入边集，并把端点加入点集。
 *)

Definition add_edge_graph (g : G) (u v : V) (e : E) : G :=
  mkG
    (graph_weight g)
    (u :: v :: graph_vertices g)
    (e :: graph_edges g).

Definition remove_edge_graph (g : G) (e : E) : G :=
  mkG
    (graph_weight g)
    (graph_vertices g)
    (filter (fun a => if E_eq_dec a e then false else true) (graph_edges g)).

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

Lemma add_edge_graph_step :
  forall g u v e x y a,
    gvalid g ->
    vvalid g u ->
    ~ evalid g e ->
    edge_connects e u v ->
    step_aux (add_edge_graph g u v e) a x y <->
      step_aux g a x y \/
      (a = e /\ ((x = u /\ y = v) \/ (x = v /\ y = u))).
Proof.
  intros g u v e x y a Hg Hu Hne Hconn.
  unfold step_aux, graph_instance, graph_step, add_edge_graph; simpl.
  split.
  - intros [[Ha | Ha] [Hends Hxy]].
    + subst a.
      right; split; [reflexivity|].
      unfold edge_connects in Hconn.
      destruct Hconn as [[Hsu Htv] | [Hsv Htu]];
        destruct Hxy as [[Hx Hy] | [Hx Hy]];
        subst; auto.
    + left.
      destruct (Hg a Ha) as [p [q [_ [Hends_old _]]]].
      split; [exact Ha|split; [exact Hends_old|exact Hxy]].
  - intros [Hold | [Ha Hxy]].
    + destruct Hold as [Ha [Hends Hxy]].
      split; [right; exact Ha|].
      split.
      * destruct Hends as [Hsrc Hdst]; split; simpl; auto.
      * exact Hxy.
    + subst a.
      split; [left; reflexivity|].
      split.
      * unfold edge_connects in Hconn.
        destruct Hconn as [[<- <-] | [<- <-]];
          split; simpl; auto.
      * unfold edge_connects in Hconn.
        destruct Hconn as [[Hsu Htv] | [Hsv Htu]];
          destruct Hxy as [[-> ->] | [-> ->]];
          subst; auto.
Qed.

Lemma add_edge_graph_addEdge :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    ~ evalid g e ->
    edge_connects e u v ->
    addEdge g (add_edge_graph g u v e) u v e.
Proof.
  intros g u v e Hg Hu Hne Hconn.
  constructor.
  - intros x. apply add_edge_graph_vvalid.
  - intros a. apply add_edge_graph_evalid_any.
  - intros x y a. apply add_edge_graph_step; auto.
Qed.

Lemma graph_step_edge_connects :
  forall g e u v,
    step_aux g e u v ->
    edge_connects e u v.
Proof.
  intros g e u v Hstep.
  unfold step_aux, graph_instance, graph_step in Hstep.
  destruct Hstep as [_ [_ Huv]].
  unfold edge_connects, edge_src, edge_dst in *.
  destruct Huv as [[Hu Hv] | [Hu Hv]].
  - left; split; symmetry; assumption.
  - right; split; symmetry; assumption.
Qed.

Lemma add_edge_graph_gvalid :
  forall g u v e,
    gvalid g ->
    edge_connects e u v ->
    gvalid (add_edge_graph g u v e).
Proof.
  intros g u v e Hg Hconn.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  unfold add_edge_graph in Ha; simpl in Ha.
  destruct Ha as [Ha_new | Ha_old].
  - subst a.
    exists u, v.
    unfold step_aux, graph_instance, graph_step, add_edge_graph; simpl.
    split; [left; reflexivity|].
    split.
    + unfold edge_endpoints_valid, edge_src, edge_dst.
      unfold edge_connects in Hconn.
      destruct Hconn as [[<- <-] | [<- <-]]; simpl; split; auto.
    + unfold edge_connects in Hconn.
      destruct Hconn as [[Hsu Htv] | [Hsv Htu]];
        subst; simpl; auto.
  - destruct (Hg a Ha_old) as [x [y Hstep]].
    exists x, y.
    destruct Hstep as [_ [Hends Hxy]].
    unfold step_aux, graph_instance, graph_step, add_edge_graph; simpl.
    split; [right; exact Ha_old|].
    split.
    + destruct Hends as [Hsrc Hdst]; split; simpl; auto.
    + exact Hxy.
Qed.

Lemma add_edge_graph_gvalid_new_vertex :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    ~ vvalid g v ->
    edge_connects e u v ->
    gvalid (add_edge_graph g u v e).
Proof.
  intros g u v e Hg Hu Hvout Hconn.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  unfold add_edge_graph in Ha; simpl in Ha.
  destruct Ha as [Ha_new | Ha_old].
  - subst a.
    exists u, v.
    unfold step_aux, graph_instance, graph_step, add_edge_graph; simpl.
    split; [left; reflexivity|].
    split.
    + unfold edge_endpoints_valid, edge_src, edge_dst in *.
      destruct Hconn as [[<- <-] | [<- <-]]; simpl; split; auto.
    + unfold edge_connects in Hconn.
      destruct Hconn as [[Hsu Htv] | [Hsv Htu]];
        subst; simpl; auto.
  - destruct (Hg a Ha_old) as [x [y Hstep]].
    exists x, y.
    destruct Hstep as [_ [Hends Hxy]].
    unfold step_aux, graph_instance, graph_step, add_edge_graph; simpl.
    split; [right; exact Ha_old|].
    split.
    + destruct Hends as [Hsrc Hdst]; split; simpl; auto.
    + exact Hxy.
Qed.

Lemma add_edge_graph_vertex_num_new_vertex :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    ~ vvalid g v ->
    edge_connects e u v ->
    vertex_num (add_edge_graph g u v e) = vertex_num g + 1.
Proof.
  intros g u v e Hg Hu Hvout Hconn.
  pose proof (add_edge_graph_gvalid_new_vertex g u v e Hg Hu Hvout Hconn) as Hgadd.
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
  unfold evalid, graph_instance, remove_edge_graph; simpl.
  split.
  - intros Hin.
    apply filter_In in Hin as [Hin Hfilter].
    destruct (E_eq_dec a e) as [Ha | Ha]; [discriminate |].
    split; auto.
  - intros [Hin Hneq].
    apply filter_In.
    split; [exact Hin |].
    destruct (E_eq_dec a e) as [Ha | Ha]; [contradiction | reflexivity].
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
  destruct (E_eq_dec a e) as [Ha | Ha].
  - subst a.
    unfold step_aux, graph_instance, graph_step.
    split.
    + intros Hcur.
      right; split; [reflexivity |].
      pose proof (step_aux_unique_undirected g e u v x y Hg Hstep Hcur)
        as [[-> ->] | [-> ->]]; auto.
    + intros [Hremove | [_ Hxy]].
      * destruct Hremove as [Hin _].
        unfold remove_edge_graph in Hin; simpl in Hin.
        apply filter_In in Hin as [_ Hfilter].
        destruct (E_eq_dec e e) as [_ | Hbad];
          [discriminate | exfalso; apply Hbad; reflexivity].
      * destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep |].
        change (step_aux g e v u).
        apply step_sym; exact Hstep.
  - split.
    + intros Hcur.
      destruct Hcur as [Hea [Hends Hxy]].
      left.
      unfold step_aux, graph_instance, graph_step, remove_edge_graph.
      simpl.
      split.
      * apply filter_In.
        split; [exact Hea |].
        destruct (E_eq_dec a e) as [Heq | _]; [contradiction | reflexivity].
      * split; [exact Hends | exact Hxy].
    + intros [Hremove | [Heq _]].
      * unfold step_aux, graph_instance, graph_step, remove_edge_graph in Hremove.
        simpl in Hremove.
        destruct Hremove as [Hin [Hends Hxy]].
        apply filter_In in Hin as [Hea _].
        unfold step_aux, graph_instance, graph_step.
        split; [exact Hea | split; auto].
      * contradiction.
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
  destruct (E_eq_dec a e) as [Ha_eq | Ha_neq]; [discriminate|].
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
    assert (Hconn : edge_connects e u v)
      by (apply graph_step_edge_connects with (g := g); exact Hstep).
    split.
    + apply add_edge_graph_gvalid; auto.
    + split.
      * apply add_edge_graph_addEdge; auto.
      * constructor.
        -- intros z Hz.
        rewrite add_edge_graph_vvalid in Hz.
        destruct Hz as [Hz | [-> | ->]].
        ++ apply Hsub; exact Hz.
        ++ apply Hsub; exact Hu.
        ++ apply Hsub; exact Hv.
        -- intros x y a Ha.
        rewrite add_edge_graph_step in Ha by auto.
        destruct Ha as [Ha_old | [Ha_new Hxy]].
        ++ apply Hsub; exact Ha_old.
        ++ subst a.
           destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
           apply step_sym; exact Hstep.
  - intros g s u v e Hg Hs Hsub Hstep Hu Hvout Hne.
    exists (add_edge_graph s u v e).
    assert (Hconn : edge_connects e u v)
      by (apply graph_step_edge_connects with (g := g); exact Hstep).
    split.
    + apply add_edge_graph_gvalid; auto.
    + split.
      * apply add_edge_graph_addEdge; auto.
      * constructor.
        -- intros z Hz.
        rewrite add_edge_graph_vvalid in Hz.
        destruct Hz as [Hz | [-> | ->]].
        ++ apply Hsub; exact Hz.
        ++ apply Hsub; exact Hu.
        ++ eapply step_vvalid2; eauto.
        -- intros x y a Ha.
        rewrite add_edge_graph_step in Ha by auto.
        destruct Ha as [Ha_old | [Ha_new Hxy]].
        ++ apply Hsub; exact Ha_old.
        ++ subst a.
           destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
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
           destruct (E_eq_dec a e) as [-> | Hneq]; auto.
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
    right; split; [reflexivity | auto].
Qed.

Definition Prim2 (g : G) : program St unit :=
  @Prim.Prim2 G V E graph_instance gvalid_instance finite_instance
    g edge_weight_instance.

Lemma Prim2_correct_concrete :
  forall g src,
    PrimEnv g src ->
    Hoare (initStPred g src) (Prim2 g)
      (fun _ s => return_is_mst g s.(Prim.graph_in_state)).
Proof.
  intros g src Henv.
  destruct Henv as [Hg Hsrc Hconn].
  unfold initStPred, Prim2, initSt, return_is_mst.
  eapply (@Prim.Prim2_correct
    G V E graph_instance gvalid_instance
    stepvalid_instance noempty_instance undirected_instance stepunique_instance
    finite_instance elist_bijective_instance
    g
    P path_instance emptypath_instance singlepath_instance concatpath_instance
    destruct1npath_instance tree_instance
    edge_weight_instance
    Hconn
    src Hsrc Hg
    addEdgeInSubgraph_instance addEdgeGValid_instance
    (emptyGraph_instance g src)).
Qed.

Definition Prim2_loop (g : G) (i : Z) : program St unit :=
  @range_iter St unit
    i
    (Zlength (bijective_listV g) - 1)
    (fun _ _ =>
       @Prim.Prim_body G V E graph_instance g edge_weight_instance)
    tt.

Lemma initStPred_Prim2_to_loop0 :
  forall g src X,
    safeExec (initStPred g src) (Prim2 g) X ->
    safeExec (prim_state_is (initSt g src)) (Prim2_loop g 0) X.
Proof.
  intros g src X Hsafe.
  unfold initStPred, prim_state_is, Prim2, Prim2_loop in *.
  exact Hsafe.
Qed.
















(** ** 邻接矩阵数组的下标语义

    C 侧采用 [int** graph]，规格侧用 [list (list Z)] 表示矩阵。
    因此抽象读取就是先取第 [u] 行，再取第 [v] 列。
 *)

Definition matrix_index_valid (n u v : Z) : Prop :=
  0 <= u < n /\ 0 <= v < n.

Definition matrix_entry (matrix : list (list Z)) (u v : V) : Z :=
  Znth v (Znth u matrix nil) 0.

Definition adjacency_matrix_shape (n : Z) (matrix : list (list Z)) : Prop :=
  Zlength matrix = n /\
  forall u, 0 <= u < n -> Zlength (Znth u matrix nil) = n.

Definition adjacency_matrix_model (n : Z) (matrix : list (list Z)) (g : G) (inf : Z) : Prop :=
  adjacency_matrix_shape n matrix /\
  (forall v, In v (graph_vertices g) <-> In v (Zrange 0 n)) /\
	  (forall u v,
	     0 <= u < n ->
	     0 <= v < n ->
	     matrix_entry matrix u v = inf \/
	     0 <= matrix_entry matrix u v < inf) /\
  graph_wf g /\
  (forall e,
     In e (graph_edges g) ->
     matrix_index_valid n (edge_src g e) (edge_dst g e) /\
     graph_weight g e = matrix_entry matrix (edge_src g e) (edge_dst g e) /\
     graph_weight g e = matrix_entry matrix (edge_dst g e) (edge_src g e) /\
     graph_weight g e <> inf) /\
  (forall u v,
     0 <= u < n ->
     0 <= v < n ->
     matrix_entry matrix u v <> inf ->
	     In (undirected_edge u v) (graph_edges g) /\
	     graph_step g (undirected_edge u v) u v /\
	     graph_weight g (undirected_edge u v) = matrix_entry matrix u v).

Definition prim_adjacency_matrix_graph_model
    (n : Z) (g : G) (inf : Z) (matrix : list (list Z)) : Prop :=
  adjacency_matrix_model n matrix g inf.

Lemma vertex_parent_matches_default_edge_parent :
  forall n matrix g inf src,
    adjacency_matrix_model n matrix g inf ->
    vertex_parent_matches_edge_parent g
      src
      (repeat_Z (-1) n)
      (default_edge_list n).
Proof.
  intros n matrix g inf src Hmodel v Hv.
  assert (Hv_range : 0 <= v < n).
  {
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [_ [Hvertices _]].
    apply Hvertices in Hv.
    rewrite <- In_Zrange in Hv.
    exact Hv.
  }
  split.
  - unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
  - split.
    + unfold default_edge_list. rewrite Zlength_correct, repeat_length. lia.
    + split.
      * intros _. unfold repeat_Z, default_edge_list.
        rewrite !Znth_repeat_lt by lia.
        split; reflexivity.
      * left.
      unfold repeat_Z, default_edge_list.
      rewrite !Znth_repeat_lt by lia.
      split; reflexivity.
Qed.

Lemma adjacency_matrix_vertex_in_graph :
  forall n matrix g inf v,
    adjacency_matrix_model n matrix g inf ->
    0 <= v < n ->
    In v (graph_vertices g).
Proof.
  intros n matrix g inf v Hmodel Hv.
  unfold adjacency_matrix_model in Hmodel.
  destruct Hmodel as [_ [Hvertices _]].
  apply Hvertices.
  rewrite <- In_Zrange.
  exact Hv.
Qed.

Lemma vertex_parent_matches_edge_parent_update_matrix :
  forall n matrix g inf src vertex_parent edge_parent minIndex j,
    adjacency_matrix_model n matrix g inf ->
    vertex_parent_matches_edge_parent g src vertex_parent edge_parent ->
    0 <= minIndex < n ->
    0 <= j < n ->
    minIndex <> j ->
    j <> src ->
    matrix_entry matrix minIndex j <> inf ->
    vertex_parent_matches_edge_parent g
      src
      (replace_Znth j minIndex vertex_parent)
      (replace_Znth j (undirected_edge minIndex j) edge_parent).
Proof.
  intros n matrix g inf src vertex_parent edge_parent minIndex j
         Hmodel Hmatch Hmin Hj Hneq Hj_src Hedge v Hv.
  assert (Hj_graph : In j (graph_vertices g)).
  {
    eapply adjacency_matrix_vertex_in_graph; eauto.
  }
  pose proof (Hmatch j Hj_graph) as [Hvp_j [Hep_j [_ _]]].
  destruct (Z.eq_dec v j) as [-> | Hvj].
  - split.
    { rewrite Zlength_replace_Znth_local; lia. }
    split.
    { rewrite Zlength_replace_Znth; lia. }
    assert (Hmin_graph : In minIndex (graph_vertices g)).
    {
      eapply adjacency_matrix_vertex_in_graph; eauto.
    }
    rewrite (Znth_replace_Znth_same_any vertex_parent j minIndex (-1)) by lia.
    split.
    { intros Hsrc. subst j. contradiction. }
    right.
    split; [lia|].
    split; [exact Hmin_graph|].
    split; [exact Hneq|].
    split.
    { rewrite (Znth_replace_Znth_same_any edge_parent j (undirected_edge minIndex j) default_edge) by lia.
      reflexivity. }
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [_ [_ [_ [_ [_ Hedges]]]]].
    specialize (Hedges minIndex j Hmin Hj Hedge).
    destruct Hedges as [_ [Hstep _]].
    rewrite <- (Znth_replace_Znth_same_any edge_parent j (undirected_edge minIndex j) default_edge) in Hstep by lia.
    exact Hstep.
  - specialize (Hmatch v Hv) as [Hvp [Hep Hbody]].
    split.
    { rewrite Zlength_replace_Znth_local; lia. }
    split.
    { rewrite Zlength_replace_Znth; lia. }
    rewrite (Znth_replace_Znth_diff_any vertex_parent j v minIndex (-1)) by lia.
    rewrite <- (Znth_replace_Znth_diff_any edge_parent j v (undirected_edge minIndex j) default_edge) in Hbody by lia.
    destruct Hbody as [Hsrc_empty Hbody].
    split.
    { intros Hv_src.
      specialize (Hsrc_empty Hv_src).
      exact Hsrc_empty. }
    exact Hbody.
Qed.

(** 最终返回值与结果图的关系。

    当前邻接矩阵版 C 程序返回的是 MST 的总权重，
    因此这里把返回整数 [ret] 解释为结果图 [rg] 中所有合法边权重之和。
 *)
Definition graph_total_weight (g : G) : Z :=
  fold_right Z.add 0 (map (graph_weight g) (valid_edges g)).

Lemma graph_total_weight_add_edge_graph :
  forall h u v e,
    ~ evalid h e ->
    graph_total_weight (add_edge_graph h u v e) =
    graph_weight h e + graph_total_weight h.
Proof.
  intros h u v e Hnotin.
  unfold graph_total_weight, valid_edges, add_edge_graph.
  simpl.
  unfold evalid, graph_instance in Hnotin; simpl in Hnotin.
  destruct (in_dec E_eq_dec e (graph_edges h)) as [Hin | Hnin].
  - exfalso. apply Hnotin. exact Hin.
  - simpl. reflexivity.
Qed.

Definition prim_result_weight (rg : G) (ret : Z) : Prop :=
  ret = graph_total_weight rg.

Definition inf_matrix (rows cols inf : Z) : list (list Z) :=
  repeat (repeat_Z inf cols) (Z.to_nat rows).

Definition set_matrix_entry
    (matrix : list (list Z)) (u v value : Z) : list (list Z) :=
  replace_Znth u
    (replace_Znth v value (Znth u matrix nil))
    matrix.

Definition set_undirected_matrix_entry
    (matrix : list (list Z)) (u v value : Z) : list (list Z) :=
  set_matrix_entry (set_matrix_entry matrix u v value) v u value.

Lemma set_matrix_entry_shape :
  forall n matrix u v value,
    adjacency_matrix_shape n matrix ->
    0 <= u < n ->
    adjacency_matrix_shape n (set_matrix_entry matrix u v value).
Proof.
  intros n matrix u v value Hshape Hu.
  unfold adjacency_matrix_shape in *.
  destruct Hshape as [Hlen Hrows].
  unfold set_matrix_entry.
  split.
  - rewrite Zlength_replace_Znth_local. exact Hlen.
  - intros r Hr.
    destruct (Z.eq_dec r u) as [-> | Hru].
    + rewrite Znth_replace_Znth_same_any by lia.
      rewrite Zlength_replace_Znth_local.
      apply Hrows. exact Hu.
    + rewrite Znth_replace_Znth_diff_any by lia.
      apply Hrows. exact Hr.
Qed.

Lemma set_undirected_matrix_entry_shape :
  forall n matrix u v value,
    adjacency_matrix_shape n matrix ->
    0 <= u < n ->
    0 <= v < n ->
    adjacency_matrix_shape n (set_undirected_matrix_entry matrix u v value).
Proof.
  intros n matrix u v value Hshape Hu Hv.
  unfold set_undirected_matrix_entry.
  apply set_matrix_entry_shape; auto.
  apply set_matrix_entry_shape; auto.
Qed.

Lemma matrix_entry_set_matrix_entry_same :
  forall n matrix u v value,
    adjacency_matrix_shape n matrix ->
    0 <= u < n ->
    0 <= v < n ->
    matrix_entry (set_matrix_entry matrix u v value) u v = value.
Proof.
  intros n matrix u v value Hshape Hu Hv.
  unfold matrix_entry, set_matrix_entry.
  rewrite Znth_replace_Znth_same_any by
    (unfold adjacency_matrix_shape in Hshape; destruct Hshape as [Hlen _]; lia).
  rewrite Znth_replace_Znth_same_local by
    (unfold adjacency_matrix_shape in Hshape; destruct Hshape as [_ Hrows];
     rewrite Hrows by exact Hu; exact Hv).
  reflexivity.
Qed.

Lemma matrix_entry_set_matrix_entry_diff :
  forall n matrix row col u v value,
    adjacency_matrix_shape n matrix ->
    0 <= row < n ->
    0 <= col < n ->
    0 <= u < n ->
    0 <= v < n ->
    (row <> u \/ col <> v) ->
    matrix_entry (set_matrix_entry matrix u v value) row col =
    matrix_entry matrix row col.
Proof.
  intros n matrix row col u v value Hshape Hrow Hcol Hu Hv Hdiff.
  unfold matrix_entry, set_matrix_entry.
  destruct (Z.eq_dec row u) as [-> | Hrowu].
  - destruct Hdiff as [Hbad | Hcolv]; [contradiction|].
    rewrite Znth_replace_Znth_same_any by
      (unfold adjacency_matrix_shape in Hshape; destruct Hshape as [Hlen _]; lia).
    rewrite Znth_replace_Znth_diff_local.
    + reflexivity.
    + unfold adjacency_matrix_shape in Hshape.
      destruct Hshape as [_ Hrows].
      rewrite Hrows by exact Hu.
      exact Hv.
    + unfold adjacency_matrix_shape in Hshape.
      destruct Hshape as [_ Hrows].
      rewrite Hrows by exact Hu.
      exact Hcol.
    + intro Heq. apply Hcolv. symmetry. exact Heq.
  - rewrite Znth_replace_Znth_diff_any by
      (unfold adjacency_matrix_shape in Hshape; destruct Hshape as [Hlen _]; lia).
    reflexivity.
Qed.

Lemma matrix_entry_set_undirected_matrix_entry_left :
  forall n matrix u v value,
    adjacency_matrix_shape n matrix ->
    0 <= u < n ->
    0 <= v < n ->
    matrix_entry (set_undirected_matrix_entry matrix u v value) u v = value.
Proof.
  intros n matrix u v value Hshape Hu Hv.
  unfold set_undirected_matrix_entry.
  destruct (Z.eq_dec u v) as [-> | Huv].
  - eapply matrix_entry_set_matrix_entry_same; eauto.
    eapply set_matrix_entry_shape; eauto.
  - rewrite matrix_entry_set_matrix_entry_diff
      with (n := n) (u := v) (v := u) by
        (try apply set_matrix_entry_shape; auto; lia).
    eapply matrix_entry_set_matrix_entry_same; eauto.
Qed.

Lemma matrix_entry_set_undirected_matrix_entry_right :
  forall n matrix u v value,
    adjacency_matrix_shape n matrix ->
    0 <= u < n ->
    0 <= v < n ->
    matrix_entry (set_undirected_matrix_entry matrix u v value) v u = value.
Proof.
  intros n matrix u v value Hshape Hu Hv.
  unfold set_undirected_matrix_entry.
  eapply matrix_entry_set_matrix_entry_same.
  - eapply set_matrix_entry_shape; eauto.
  - exact Hv.
  - exact Hu.
Qed.

Lemma matrix_entry_set_undirected_matrix_entry_diff :
  forall n matrix row col u v value,
    adjacency_matrix_shape n matrix ->
    0 <= row < n ->
    0 <= col < n ->
    0 <= u < n ->
    0 <= v < n ->
    (row <> u \/ col <> v) ->
    (row <> v \/ col <> u) ->
    matrix_entry (set_undirected_matrix_entry matrix u v value) row col =
    matrix_entry matrix row col.
Proof.
  intros n matrix row col u v value Hshape Hrow Hcol Hu Hv Hdiff1 Hdiff2.
  unfold set_undirected_matrix_entry.
  rewrite matrix_entry_set_matrix_entry_diff
    with (n := n) (u := v) (v := u).
  - eapply matrix_entry_set_matrix_entry_diff; eauto.
  - eapply set_matrix_entry_shape; eauto.
  - exact Hrow.
  - exact Hcol.
  - exact Hv.
  - exact Hu.
  - exact Hdiff2.
Qed.

Definition processed_parent_edge_cell
    (g : G) (vertex_parent : list Z) (edge_parent : list E)
    (i u v w : Z) : Prop :=
  exists child parent e,
    In child (Zrange 0 i) /\
    In child (graph_vertices g) /\
    parent = Znth child vertex_parent (-1) /\
    parent <> -1 /\
    e = Znth child edge_parent default_edge /\
    e = undirected_edge parent child /\
    undirected_edge u v = e /\
    graph_step g e parent child /\
    graph_weight g e = w.

(** 构造返回矩阵时的前缀规格。

    [i]表示已经处理了顶点编号区间[0, i)。
    对任意矩阵格子[(u,v)]：
    - 如果它对应某个已处理点[child]的父边，则该格子必须等于这条父边权重；
    - 如果它不对应任何已处理父边，则该格子必须仍然是[inf]。

    这个谓词用于后处理循环；它需要[input_matrix]，因为C代码实际从
    [graph[p][v]]读取权重再写入[result_matrix]。
 *)
Definition result_matrix_parent_prefix
    (g : G) (src : V) (input_matrix result_matrix : list (list Z))
    (vertex_parent : list Z) (edge_parent : list E)
    (inf i : Z) : Prop :=
  adjacency_matrix_shape (Zlength input_matrix) result_matrix /\
  vertex_parent_matches_edge_parent g src vertex_parent edge_parent /\
  forall u v,
    In u (graph_vertices g) ->
    In v (graph_vertices g) ->
    (exists w,
       processed_parent_edge_cell g vertex_parent edge_parent i u v w /\
       matrix_entry result_matrix u v = w /\
       matrix_entry input_matrix u v = w) \/
    ((forall w,
        ~ processed_parent_edge_cell g vertex_parent edge_parent i u v w) /\
       matrix_entry result_matrix u v = inf).

Lemma inf_matrix_shape :
  forall n inf,
    0 <= n ->
    adjacency_matrix_shape n (inf_matrix n n inf).
Proof.
  intros n inf Hn.
  unfold adjacency_matrix_shape, inf_matrix.
  split.
  - rewrite Zlength_correct, repeat_length. lia.
  - intros u Hu.
    rewrite Znth_repeat_lt.
    + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
    + lia.
Qed.

Lemma matrix_entry_inf_matrix :
  forall n inf u v,
    0 <= n ->
    0 <= u < n ->
    0 <= v < n ->
    matrix_entry (inf_matrix n n inf) u v = inf.
Proof.
  intros n inf u v Hn Hu Hv.
  unfold matrix_entry, inf_matrix.
  rewrite Znth_repeat_lt.
  - unfold repeat_Z.
    rewrite Znth_repeat_lt; lia.
  - lia.
Qed.

Lemma processed_parent_edge_cell_zero_false :
  forall g vertex_parent edge_parent u v w,
    ~ processed_parent_edge_cell g vertex_parent edge_parent 0 u v w.
Proof.
  intros g vertex_parent edge_parent u v w Hcell.
  unfold processed_parent_edge_cell in Hcell.
  destruct Hcell as [child [parent [e [Hin _]]]].
  rewrite <- In_Zrange in Hin.
  lia.
Qed.

Lemma result_matrix_parent_prefix_zero_inf_matrix :
  forall n input_matrix g src vertex_parent edge_parent inf,
    0 <= n ->
    adjacency_matrix_model n input_matrix g inf ->
    vertex_parent_matches_edge_parent g src vertex_parent edge_parent ->
    result_matrix_parent_prefix g src input_matrix (inf_matrix n n inf)
      vertex_parent edge_parent inf 0.
Proof.
  intros n input_matrix g src vertex_parent edge_parent inf Hn Hmodel Hparent.
  unfold result_matrix_parent_prefix.
  unfold adjacency_matrix_model in Hmodel.
  destruct Hmodel as [[Hmatrix_len _] [Hvertices _]].
  rewrite Hmatrix_len.
  split.
  - apply inf_matrix_shape; exact Hn.
  - split; [exact Hparent|].
    intros u v Hu Hv.
    right.
    split.
    + intros w Hcell.
      exact (processed_parent_edge_cell_zero_false _ _ _ _ _ _ Hcell).
    + apply matrix_entry_inf_matrix.
      * exact Hn.
      * apply Hvertices in Hu. rewrite <- In_Zrange in Hu. exact Hu.
      * apply Hvertices in Hv. rewrite <- In_Zrange in Hv. exact Hv.
Qed.

Lemma processed_parent_edge_cell_skip_invalid_parent_false :
  forall n input_matrix g src vertex_parent edge_parent inf i u v w,
    adjacency_matrix_model n input_matrix g inf ->
    vertex_parent_matches_edge_parent g src vertex_parent edge_parent ->
    0 <= i < n ->
    (Znth i vertex_parent (-1) < 0 \/ n <= Znth i vertex_parent (-1)) ->
    (forall w, ~ processed_parent_edge_cell g vertex_parent edge_parent i u v w) ->
    ~ processed_parent_edge_cell g vertex_parent edge_parent (i + 1) u v w.
Proof.
  intros n input_matrix g src vertex_parent edge_parent inf i u v w
         Hmodel Hparent Hi Hinvalid Hnone Hcell.
  unfold processed_parent_edge_cell in Hcell.
  destruct Hcell as [child [parent [e [Hchild [Hchild_graph Hrest]]]]].
  rewrite Zrange_0_snoc in Hchild by lia.
  apply in_app_or in Hchild.
  destruct Hchild as [Hold | Hnew].
  - apply (Hnone w).
    unfold processed_parent_edge_cell.
    exists child, parent, e.
    split; [exact Hold|].
    split; [exact Hchild_graph|].
    exact Hrest.
  - simpl in Hnew. destruct Hnew as [Hchild_i | []].
    subst child.
    destruct Hrest as [Hparent_eq [Hparent_not_none _]].
    assert (Hi_graph : In i (graph_vertices g)).
    {
      unfold adjacency_matrix_model in Hmodel.
      destruct Hmodel as [_ [Hvertices _]].
      apply Hvertices. rewrite <- In_Zrange. exact Hi.
    }
    specialize (Hparent i Hi_graph) as [_ [_ [Hsrc_case Hbody]]].
    destruct Hinvalid as [Hlt | Hge].
    + destruct Hbody as [[Hp _] | [Hp_ne [Hp_graph _]]].
      * rewrite <- Hparent_eq in Hp. lia.
      * unfold adjacency_matrix_model in Hmodel.
        destruct Hmodel as [_ [Hvertices _]].
        apply Hvertices in Hp_graph.
        rewrite <- In_Zrange in Hp_graph.
        rewrite <- Hparent_eq in Hp_graph.
        lia.
    + destruct Hbody as [[Hp _] | [Hp_ne [Hp_graph _]]].
      * rewrite <- Hparent_eq in Hp. lia.
      * unfold adjacency_matrix_model in Hmodel.
        destruct Hmodel as [_ [Hvertices _]].
        apply Hvertices in Hp_graph.
        rewrite <- In_Zrange in Hp_graph.
        rewrite <- Hparent_eq in Hp_graph.
        lia.
Qed.

Lemma result_matrix_parent_prefix_skip_invalid_parent :
  forall n input_matrix result_matrix g src vertex_parent edge_parent inf i,
    adjacency_matrix_model n input_matrix g inf ->
    result_matrix_parent_prefix g src input_matrix result_matrix
      vertex_parent edge_parent inf i ->
    0 <= i < n ->
    (Znth i vertex_parent (-1) < 0 \/ n <= Znth i vertex_parent (-1)) ->
    result_matrix_parent_prefix g src input_matrix result_matrix
      vertex_parent edge_parent inf (i + 1).
Proof.
  intros n input_matrix result_matrix g src vertex_parent edge_parent inf i
         Hmodel Hprefix Hi Hinvalid.
  unfold result_matrix_parent_prefix in *.
  destruct Hprefix as [Hshape [Hparent Hcells]].
  split; [exact Hshape|].
  split; [exact Hparent|].
  intros u v Hu Hv.
  destruct (Hcells u v Hu Hv) as [[w [Hcell [Hres Hinput]]] | [Hnone Hres]].
  - left.
    exists w.
    split.
    + unfold processed_parent_edge_cell in *.
      destruct Hcell as [child [parent [e [Hchild Hrest]]]].
      exists child, parent, e.
      split.
      * rewrite <- In_Zrange in Hchild.
        rewrite <- In_Zrange.
        lia.
      * exact Hrest.
    + split; assumption.
  - right.
    split.
    + intros w Hcell.
      eapply processed_parent_edge_cell_skip_invalid_parent_false; eauto.
    + exact Hres.
Qed.

Lemma result_matrix_parent_prefix_skip_negative_parent :
  forall n input_matrix result_matrix g src vertex_parent edge_parent inf i,
    adjacency_matrix_model n input_matrix g inf ->
    result_matrix_parent_prefix g src input_matrix result_matrix
      vertex_parent edge_parent inf i ->
    0 <= i < n ->
    Znth i vertex_parent (-1) < 0 ->
    result_matrix_parent_prefix g src input_matrix result_matrix
      vertex_parent edge_parent inf (i + 1).
Proof.
  intros.
  eapply result_matrix_parent_prefix_skip_invalid_parent; eauto.
Qed.

Lemma result_matrix_parent_prefix_skip_large_parent :
  forall n input_matrix result_matrix g src vertex_parent edge_parent inf i,
    adjacency_matrix_model n input_matrix g inf ->
    result_matrix_parent_prefix g src input_matrix result_matrix
      vertex_parent edge_parent inf i ->
    0 <= i < n ->
    n <= Znth i vertex_parent (-1) ->
    result_matrix_parent_prefix g src input_matrix result_matrix
      vertex_parent edge_parent inf (i + 1).
Proof.
  intros.
  eapply result_matrix_parent_prefix_skip_invalid_parent; eauto.
Qed.

Lemma result_matrix_parent_prefix_step :
  forall n input_matrix result_matrix g src vertex_parent edge_parent inf i p w,
    adjacency_matrix_model n input_matrix g inf ->
    result_matrix_parent_prefix g src input_matrix result_matrix
      vertex_parent edge_parent inf i ->
    0 <= i < n ->
    0 <= p < n ->
    p = Znth i vertex_parent (-1) ->
    w = matrix_entry input_matrix p i ->
    result_matrix_parent_prefix g src input_matrix
      (set_undirected_matrix_entry result_matrix p i w)
      vertex_parent edge_parent inf (i + 1).
Proof.
  intros n input_matrix result_matrix g src vertex_parent edge_parent inf i p w
         Hmodel Hprefix Hi Hp Hp_eq Hw_eq.
  unfold result_matrix_parent_prefix in Hprefix.
  destruct Hprefix as [Hshape_result [Hparent Hcells]].
  unfold adjacency_matrix_model in Hmodel.
  destruct Hmodel as [Hshape_input [Hvertices [Hentry_bound [Hwf_g [Hedge_g Hcomplete]]]]].
  assert (Hi_graph : In i (graph_vertices g)).
  { apply Hvertices. rewrite <- In_Zrange. exact Hi. }
  assert (Hp_graph : In p (graph_vertices g)).
  { apply Hvertices. rewrite <- In_Zrange. exact Hp. }
  pose proof (Hparent i Hi_graph) as [_ [_ [Hsrc_empty Hparent_i]]].
  assert (Hp_ne_i : p <> i).
  {
    destruct Hparent_i as [[Hp_none _] | [Hp_not_none [_ [Hp_ne_i0 _]]]].
    - rewrite <- Hp_eq in Hp_none. lia.
    - rewrite <- Hp_eq in Hp_ne_i0. exact Hp_ne_i0.
  }
  assert (Hstep_pi : graph_step g (undirected_edge p i) p i).
  {
    destruct Hparent_i as [[Hp_none _] | [Hp_not_none [_ [Hp_ne_i0 [Heq_edge Hstep]]]]].
    - rewrite <- Hp_eq in Hp_none. lia.
    - rewrite <- Hp_eq in Hp_ne_i0.
      rewrite <- Hp_eq in Heq_edge.
      rewrite <- Hp_eq in Hstep.
      rewrite Heq_edge in Hstep.
      exact Hstep.
  }
  assert (Hgraph_weight_pi :
    graph_weight g (undirected_edge p i) = w).
  {
    unfold graph_step in Hstep_pi.
    destruct Hstep_pi as [Hin_e [_ Hends]].
    specialize (Hedge_g (undirected_edge p i) Hin_e).
    destruct Hedge_g as [_ [Hw_src [Hw_dst _]]].
    rewrite Hw_eq.
    destruct Hends as [[Hp_src Hi_dst] | [Hp_dst Hi_src]].
    - rewrite <- Hp_src, <- Hi_dst in Hw_src.
      exact Hw_src.
    - rewrite <- Hi_src, <- Hp_dst in Hw_dst.
      exact Hw_dst.
  }
  assert (Hshape_n : adjacency_matrix_shape n result_matrix).
  {
    destruct Hshape_input as [Hinput_len _].
    rewrite <- Hinput_len.
    exact Hshape_result.
  }
  assert (Hwrite :
    forall u v,
      In u (graph_vertices g) ->
      In v (graph_vertices g) ->
      matrix_entry (set_undirected_matrix_entry result_matrix p i w) u v =
      (if E_eq_dec (undirected_edge u v) (undirected_edge p i)
       then w else matrix_entry result_matrix u v)).
  {
    intros u v Hu_g Hv_g.
    assert (Hu : 0 <= u < n).
    { apply Hvertices in Hu_g. rewrite <- In_Zrange in Hu_g. exact Hu_g. }
    assert (Hv : 0 <= v < n).
    { apply Hvertices in Hv_g. rewrite <- In_Zrange in Hv_g. exact Hv_g. }
    destruct (E_eq_dec (undirected_edge u v) (undirected_edge p i)) as [Heq | Hneq].
    - destruct (undirected_edge_eq_cases u v p i Heq) as [[-> ->] | [-> ->]].
      + eapply matrix_entry_set_undirected_matrix_entry_left; eauto.
      + eapply matrix_entry_set_undirected_matrix_entry_right; eauto.
    - rewrite matrix_entry_set_undirected_matrix_entry_diff with (n := n).
      + reflexivity.
      + exact Hshape_n.
      + exact Hu.
      + exact Hv.
      + exact Hp.
      + exact Hi.
      + destruct (Z.eq_dec u p) as [-> | Hup].
        * right. intro Hvi. subst v.
          apply Hneq. reflexivity.
        * left. exact Hup.
      + destruct (Z.eq_dec u i) as [-> | Hui].
        * right. intro Hvp. subst v.
          apply Hneq. rewrite undirected_edge_comm. reflexivity.
        * left. exact Hui.
  }
  unfold result_matrix_parent_prefix.
  split.
  - eapply set_undirected_matrix_entry_shape.
    + exact Hshape_result.
    + destruct Hshape_input as [Hinput_len _]. lia.
    + destruct Hshape_input as [Hinput_len _]. lia.
  - split; [exact Hparent|].
    intros u v Hu_g Hv_g.
    assert (Hcell_new :
      processed_parent_edge_cell g vertex_parent edge_parent (i + 1) p i w).
    {
      unfold processed_parent_edge_cell.
      exists i, p, (undirected_edge p i).
      split.
      - rewrite <- In_Zrange. lia.
      - split; [exact Hi_graph|].
        split.
        + exact Hp_eq.
        + split; [lia|].
          split.
          * destruct Hparent_i as [[Hp_none _] | [_ [_ [_ [Heq_edge _]]]]].
            { rewrite <- Hp_eq in Hp_none. lia. }
            rewrite <- Hp_eq in Heq_edge. symmetry. exact Heq_edge.
          * split; [reflexivity|].
            split; [reflexivity|].
            split; [exact Hstep_pi|].
            exact Hgraph_weight_pi.
    }
    destruct (Hcells u v Hu_g Hv_g) as [[w0 [Hcell_old [Hres_old Hinput_old]]] | [Hnone_old Hres_old]].
    + left.
      destruct (E_eq_dec (undirected_edge u v) (undirected_edge p i)) as [Heq | Hneq].
      * assert (Hw0_eq : w0 = w).
        {
          unfold processed_parent_edge_cell in Hcell_old.
          destruct Hcell_old as [child [parent [e [_ [_ [_ [_ [_ [_ [Hcanon_uv [_ Hw0]]]]]]]]]]].
          rewrite Heq in Hcanon_uv.
          rewrite <- Hcanon_uv in Hw0.
          rewrite Hgraph_weight_pi in Hw0.
          symmetry. exact Hw0.
        }
        exists w0.
        split.
        -- unfold processed_parent_edge_cell in *.
           destruct Hcell_old as [child [parent [e [Hchild Hrest]]]].
           exists child, parent, e.
           split.
           ++ rewrite <- In_Zrange in Hchild.
              rewrite <- In_Zrange.
              lia.
           ++ exact Hrest.
        -- split.
           ++ rewrite Hwrite by assumption.
              destruct (E_eq_dec (undirected_edge u v) (undirected_edge p i));
                [symmetry; exact Hw0_eq | contradiction].
           ++ exact Hinput_old.
      * exists w0.
        split.
        -- unfold processed_parent_edge_cell in *.
           destruct Hcell_old as [child [parent [e [Hchild Hrest]]]].
           exists child, parent, e.
           split.
           ++ rewrite <- In_Zrange in Hchild.
              rewrite <- In_Zrange.
              lia.
           ++ exact Hrest.
        -- split.
           ++ rewrite Hwrite by assumption.
              destruct (E_eq_dec (undirected_edge u v) (undirected_edge p i));
                [contradiction | exact Hres_old].
           ++ exact Hinput_old.
    + destruct (E_eq_dec (undirected_edge u v) (undirected_edge p i)) as [Heq | Hneq].
      * left.
        exists w.
        split.
        -- destruct (undirected_edge_eq_cases u v p i Heq) as [[-> ->] | [-> ->]].
           ++ exact Hcell_new.
           ++ unfold processed_parent_edge_cell in *.
              exists i, p, (undirected_edge p i).
              split.
              ** rewrite <- In_Zrange. lia.
              ** split; [exact Hi_graph|].
                 split; [exact Hp_eq|].
                 split; [lia|].
                 split.
                 { destruct Hparent_i as [[Hp_none _] | [_ [_ [_ [Heq_edge _]]]]].
                   - rewrite <- Hp_eq in Hp_none. lia.
                   - rewrite <- Hp_eq in Heq_edge. symmetry. exact Heq_edge. }
                 split; [reflexivity|].
                 split.
                 { rewrite undirected_edge_comm. reflexivity. }
                 split; [exact Hstep_pi|].
                 exact Hgraph_weight_pi.
        -- split.
           ++ rewrite Hwrite by assumption.
              destruct (E_eq_dec (undirected_edge u v) (undirected_edge p i));
                [reflexivity | contradiction].
	           ++ destruct (undirected_edge_eq_cases u v p i Heq) as [[-> ->] | [-> ->]].
	              ** symmetry. exact Hw_eq.
	              ** assert (Hinput_sym : matrix_entry input_matrix i p = w).
	                 {
	                   unfold graph_step in Hstep_pi.
	                   destruct Hstep_pi as [Hin_e [_ Hends]].
	                   specialize (Hedge_g (undirected_edge p i) Hin_e).
	                   destruct Hedge_g as [_ [Hw_src [Hw_dst _]]].
	                   destruct Hends as [[Hp_src Hi_dst] | [Hp_dst Hi_src]].
	                   - rewrite <- Hp_src, <- Hi_dst in Hw_dst.
	                     rewrite <- Hgraph_weight_pi.
	                     symmetry. exact Hw_dst.
	                   - rewrite <- Hi_src, <- Hp_dst in Hw_src.
	                     rewrite <- Hgraph_weight_pi.
	                     symmetry. exact Hw_src.
	                 }
	                 exact Hinput_sym.
      * right.
        split.
        -- intros w0 Hcell.
           unfold processed_parent_edge_cell in Hcell.
           destruct Hcell as [child [parent [e [Hchild Hrest]]]].
           destruct Hrest as [Hchild_graph [Hparent_eq [Hparent_not_none
             [Heq_edge [Hcanon_parent [Hcanon_uv [Hstep_child Hw_child]]]]]]].
           rewrite Zrange_0_snoc in Hchild by lia.
           apply in_app_or in Hchild.
           destruct Hchild as [Hold | Hnew].
           ++ apply (Hnone_old w0).
	              unfold processed_parent_edge_cell.
	              exists child, parent, e.
	              split; [exact Hold|].
	              split; [exact Hchild_graph|].
	              split; [exact Hparent_eq|].
	              split; [exact Hparent_not_none|].
	              split; [exact Heq_edge|].
	              split; [exact Hcanon_parent|].
	              split; [exact Hcanon_uv|].
	              split; [exact Hstep_child|].
	              exact Hw_child.
	           ++ simpl in Hnew. destruct Hnew as [Hchild_i | []].
	              subst child.
	              assert (Hparent_p : parent = p).
	              { rewrite Hparent_eq. symmetry. exact Hp_eq. }
	              subst parent.
	              rewrite Hcanon_parent in Hcanon_uv.
	              rewrite Hparent_p in Hcanon_uv.
	              apply Hneq. exact Hcanon_uv.
        -- rewrite Hwrite by assumption.
           destruct (E_eq_dec (undirected_edge u v) (undirected_edge p i));
             [contradiction | exact Hres_old].
Qed.

(** 返回二维数组版本的结果规格。

    [rg]是不是MST由[safeExec ... Prim2 ...]和Prim正确性负责；
    这里直接要求返回矩阵[result_matrix]就是[rg]的邻接矩阵表示。
 *)
Definition prim_result_matrix_matches
    (result_matrix : list (list Z)) (rg : G) (inf : Z) : Prop :=
  adjacency_matrix_model (vertex_num rg) result_matrix rg inf.

Definition prim_input_weight_bound (n inf : Z) : Prop :=
  0 <= inf /\ n * inf <= INT64_MAX.

Definition prim_result_weight_in_int64_range (rg : G) : Prop :=
  INT64_MIN <= graph_total_weight rg /\
  graph_total_weight rg <= INT64_MAX.

Definition lowcost_prefix_sum (i : Z) (lowcost : list Z) : Z :=
  fold_right Z.add 0 (map (fun v => Znth v lowcost 0) (Zrange 0 i)).

Lemma lowcost_prefix_sum_snoc :
  forall i lowcost,
    0 <= i ->
    lowcost_prefix_sum (i + 1) lowcost =
    lowcost_prefix_sum i lowcost + Znth i lowcost 0.
Proof.
  intros i lowcost Hi.
  unfold lowcost_prefix_sum.
  rewrite Zrange_0_snoc by exact Hi.
  rewrite map_app.
  simpl.
  remember (map (fun v : Z => Znth v lowcost 0) (Zrange 0 i)) as vals.
  assert (Happend :
    forall (vals' : list Z) z,
      fold_right Z.add 0 (vals' ++ [z]) =
      fold_right Z.add 0 vals' + z).
  {
    intros vals' z.
    induction vals' as [| x xs IH]; simpl; lia.
  }
  apply Happend.
Qed.

Definition lowcost_vertex_sum (vertices : list V) (lowcost : list Z) : Z :=
  fold_right Z.add 0 (map (fun v => Znth v lowcost 0) vertices).

Definition lowcost_state_sum (s : St) (lowcost : list Z) : Z :=
  lowcost_vertex_sum
    (bijective_listV s.(Prim.graph_in_state))
    lowcost.

Lemma lowcost_vertex_sum_perm :
  forall vertices1 vertices2 lowcost,
    Permutation vertices1 vertices2 ->
    lowcost_vertex_sum vertices1 lowcost =
    lowcost_vertex_sum vertices2 lowcost.
Proof.
  intros vertices1 vertices2 lowcost Hperm.
  induction Hperm; auto.
  - unfold lowcost_vertex_sum in *.
    simpl. rewrite IHHperm. reflexivity.
  - unfold lowcost_vertex_sum.
    simpl. lia.
  - etransitivity; [exact IHHperm1 | exact IHHperm2].
Qed.

Lemma lowcost_vertex_sum_replace_Znth_notin :
  forall vertices lowcost idx value,
    0 <= idx < Zlength lowcost ->
    (forall v, In v vertices -> 0 <= v < Zlength lowcost) ->
    ~ In idx vertices ->
    lowcost_vertex_sum vertices (replace_Znth idx value lowcost) =
    lowcost_vertex_sum vertices lowcost.
Proof.
  intros vertices lowcost idx value Hidx Hrange Hnotin.
  unfold lowcost_vertex_sum.
  induction vertices as [| v rest IH]; simpl; auto.
  assert (Hv_range : 0 <= v < Zlength lowcost).
  { apply Hrange. simpl; auto. }
  assert (Hidx_ne_v : idx <> v).
  { intro Hcontra. apply Hnotin. subst; simpl; auto. }
  rewrite Znth_replace_Znth_diff_local by auto.
  rewrite IH.
  - reflexivity.
  - intros x Hx. apply Hrange. simpl; auto.
  - intro Hin. apply Hnotin. simpl; auto.
Qed.

Lemma lowcost_prefix_sum_bound :
  forall lowcost bound i,
    0 <= i ->
    0 <= bound ->
    (forall v, In v (Zrange 0 i) -> 0 <= Znth v lowcost 0 <= bound) ->
    0 <= lowcost_prefix_sum i lowcost <= i * bound.
Proof.
  intros lowcost bound i Hi Hbound Hentry.
  unfold lowcost_prefix_sum.
  remember (Zrange 0 i) as vs.
  assert (Hlen : Z.of_nat (length vs) = i).
  {
    subst vs.
    rewrite <- Zlength_correct.
    rewrite Zlength_Zrange by lia.
    lia.
  }
  assert (Hall : forall v, In v vs -> 0 <= Znth v lowcost 0 <= bound).
  {
    subst vs. intros v Hv.
    apply Hentry. exact Hv.
  }
  assert (Hsum :
    0 <= fold_right Z.add 0 (map (fun v : Z => Znth v lowcost 0) vs) <=
    Z.of_nat (length vs) * bound).
  {
    clear Hentry Heqvs Hlen Hi.
    induction vs as [| v rest IH]; simpl.
    - lia.
    - assert (Hv : 0 <= Znth v lowcost 0 <= bound).
      { apply Hall. simpl; auto. }
      assert (Hrest :
        0 <= fold_right Z.add 0
          (map (fun v0 : Z => Znth v0 lowcost 0) rest) <=
        Z.of_nat (length rest) * bound).
      {
        apply IH.
        intros x Hx. apply Hall. simpl; auto.
      }
      change (Z.of_nat (length (v :: rest))) with
        (1 + Z.of_nat (length rest)).
      split.
      + lia.
      + destruct bound as [| p | p]; simpl in *.
        * lia.
        * change (Z.pos (Pos.of_succ_nat (length rest) * p)) with
            (Z.of_nat (S (length rest)) * Z.pos p).
          rewrite Nat2Z.inj_succ.
          lia.
        * lia.
  }
  rewrite Hlen in Hsum.
  exact Hsum.
Qed.

Lemma lowcost_prefix_sum_entry_safe :
  forall lowcost bound i,
    0 <= bound ->
    prim_input_weight_bound (Zlength lowcost) bound ->
    0 <= i < Zlength lowcost ->
    (forall v, 0 <= v < Zlength lowcost -> 0 <= Znth v lowcost 0 <= bound) ->
    INT64_MIN <= lowcost_prefix_sum i lowcost + Znth i lowcost 0 /\
    lowcost_prefix_sum i lowcost + Znth i lowcost 0 <= INT64_MAX.
Proof.
  intros lowcost bound i Hbound Hinput Hi Hentry.
  destruct Hinput as [_ Htotal].
  assert (Hprefix :
    0 <= lowcost_prefix_sum i lowcost <= i * bound).
  {
    apply lowcost_prefix_sum_bound; try lia.
    intros v Hv.
    rewrite <- In_Zrange in Hv.
    apply Hentry; lia.
  }
  pose proof (Hentry i Hi) as Hi_entry.
  split; [lia|].
  assert ((i + 1) * bound <= Zlength lowcost * bound).
  {
    apply Z.mul_le_mono_nonneg_r; lia.
  }
  lia.
Qed.

Lemma lowcost_entry_bound_replace_Znth :
  forall lowcost idx value bound,
    0 <= idx < Zlength lowcost ->
    0 <= value <= bound ->
    (forall v, 0 <= v < Zlength lowcost -> 0 <= Znth v lowcost 0 <= bound) ->
    forall v,
      0 <= v < Zlength (replace_Znth idx value lowcost) ->
      0 <= Znth v (replace_Znth idx value lowcost) 0 <= bound.
Proof.
  intros lowcost idx value bound Hidx Hvalue Hentry v Hv.
  rewrite Zlength_replace_Znth_local in Hv.
  destruct (Z.eq_dec v idx) as [-> | Hneq].
  - rewrite Znth_replace_Znth_same_local; auto.
  - rewrite Znth_replace_Znth_diff_local; auto.
Qed.

Definition lowcost_sum_matches_state (s : St) (lowcost : list Z) : Prop :=
  lowcost_state_sum s lowcost =
  graph_total_weight s.(Prim.graph_in_state) /\
  forall i,
    0 <= i < Zlength lowcost ->
    INT64_MIN <= lowcost_prefix_sum i lowcost + Znth i lowcost 0 /\
    lowcost_prefix_sum i lowcost + Znth i lowcost 0 <= INT64_MAX.

Definition lowcost_values_in_range (inf : Z) (lowcost : list Z) : Prop :=
  forall i,
    0 <= i < Zlength lowcost ->
    0 <= Znth i lowcost 0 <= inf.

Lemma init_lowcost_values_in_range :
  forall n inf,
    0 <= inf ->
    0 < n ->
    lowcost_values_in_range inf
      (replace_Znth 0 0 (repeat_Z inf n)).
Proof.
  intros n inf Hinf Hn i Hi.
  assert (Hlen :
    Zlength (replace_Znth 0 0 (repeat_Z inf n)) = n).
  {
    rewrite Zlength_replace_Znth.
    unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
  }
  rewrite Hlen in Hi.
  destruct (Z.eq_dec i 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_same_local.
    + lia.
    + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
  - rewrite Znth_replace_Znth_diff_local.
    + unfold repeat_Z. rewrite Znth_repeat_lt; lia.
    + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
    + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
    + lia.
Qed.

Lemma lowcost_sum_matches_state_replace_outside :
  forall g s lowcost idx value bound,
    growing_subgraph_state g s ->
    ~ vvalid s.(Prim.graph_in_state) idx ->
    0 <= idx < Zlength lowcost ->
    0 <= value <= bound ->
    prim_input_weight_bound (Zlength lowcost) bound ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost) ->
    (forall v, 0 <= v < Zlength lowcost -> 0 <= Znth v lowcost 0 <= bound) ->
    lowcost_sum_matches_state s lowcost ->
    lowcost_sum_matches_state s (replace_Znth idx value lowcost).
Proof.
  intros g s lowcost idx value bound Hstate Hidx_out Hidx Hvalue Hinput
         Hgraph_range Hentry Hsum.
  destruct Hsum as [Hsum_eq _].
  split.
  - unfold lowcost_state_sum in *.
    destruct Hstate as [Hsvalid [_ [Hsub _]]].
    rewrite lowcost_vertex_sum_replace_Znth_notin.
    + exact Hsum_eq.
    + exact Hidx.
    + intros v Hv.
      apply Hgraph_range.
      apply Hsub.
      apply (proj1 (bijective_vertices _ Hsvalid v)).
      exact Hv.
    + intro Hin.
      apply Hidx_out.
      apply (proj1 (bijective_vertices _ Hsvalid idx)).
      exact Hin.
  - intros i Hi.
    rewrite Zlength_replace_Znth_local in Hi.
    apply lowcost_prefix_sum_entry_safe with (bound := bound).
    + destruct Hinput; lia.
    + rewrite Zlength_replace_Znth_local. exact Hinput.
    + rewrite Zlength_replace_Znth_local. exact Hi.
    + apply lowcost_entry_bound_replace_Znth; auto.
Qed.

Lemma initSt_lowcost_sum_matches_state :
  forall n g src inf,
    src = 0 ->
    0 < n ->
    prim_input_weight_bound n inf ->
    lowcost_sum_matches_state
      (initSt g src)
      (replace_Znth 0 0 (repeat_Z inf n)).
Proof.
  intros n g src inf Hsrc Hn Hbound.
  split.
  - unfold lowcost_state_sum.
  assert (Hginit : gvalid (Prim.graph_in_state (initSt g src))).
  {
    unfold initSt; simpl.
    apply empty_graph_valid_of.
  }
  assert (Hperm :
    Permutation
      (bijective_listV (Prim.graph_in_state (initSt g src)))
      [src]).
  {
    apply NoDup_Permutation.
    - apply bijective_listV_NoDup; exact Hginit.
    - constructor; [intro H; inversion H | constructor].
    - intros v.
      rewrite bijective_vertices by exact Hginit.
      rewrite initSt_vvalid.
      simpl.
      split.
      + intros ->; auto.
      + intros [Hv | []]; symmetry; exact Hv.
  }
  change (
    lowcost_vertex_sum
      (bijective_listV (Prim.graph_in_state (initSt g src)))
      (replace_Znth 0 0 (repeat_Z inf n)) =
    graph_total_weight (Prim.graph_in_state (initSt g src))).
  replace (
    lowcost_vertex_sum
      (bijective_listV (Prim.graph_in_state (initSt g src)))
      (replace_Znth 0 0 (repeat_Z inf n)))
    with
      (lowcost_vertex_sum [src]
        (replace_Znth 0 0 (repeat_Z inf n))).
  2:{
    symmetry.
    apply lowcost_vertex_sum_perm.
    exact Hperm.
  }
  unfold lowcost_vertex_sum.
  simpl.
  unfold graph_total_weight, initSt, empty_graph_of, valid_edges.
  simpl.
  subst src.
    rewrite Znth_replace_Znth_Same.
    + reflexivity.
    + unfold repeat_Z.
      rewrite Zlength_correct, repeat_length.
      lia.
  - intros i Hi.
    destruct Hbound as [Hinf_nonneg Htotal_bound].
    assert (Hlen : Zlength (replace_Znth 0 0 (repeat_Z inf n)) = n).
    {
      rewrite Zlength_replace_Znth.
      { unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia. }
    }
    rewrite Hlen in Hi.
    assert (Hentry_bound :
      0 <= Znth i (replace_Znth 0 0 (repeat_Z inf n)) 0 <= inf).
    {
      destruct (Z.eq_dec i 0) as [-> | Hi0].
      - rewrite Znth_replace_Znth_Same.
        + lia.
        + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
      - rewrite Znth_replace_Znth_diff_local.
        + unfold repeat_Z. rewrite Znth_repeat_lt; lia.
        + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
        + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
        + lia.
    }
    assert (Hprefix_bound :
      0 <= lowcost_prefix_sum i (replace_Znth 0 0 (repeat_Z inf n)) <= i * inf).
    {
      apply lowcost_prefix_sum_bound; try lia.
      intros v Hv.
      rewrite <- In_Zrange in Hv.
      destruct (Z.eq_dec v 0) as [-> | Hv0].
      - rewrite Znth_replace_Znth_Same.
        + lia.
        + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
      - rewrite Znth_replace_Znth_diff_local.
        + unfold repeat_Z. rewrite Znth_repeat_lt; lia.
        + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
        + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
        + lia.
    }
    split; [lia |].
    assert (i + 1 <= n) by lia.
    assert (lowcost_prefix_sum i (replace_Znth 0 0 (repeat_Z inf n)) +
            Znth i (replace_Znth 0 0 (repeat_Z inf n)) 0 <=
            n * inf) by nia.
    lia.
Qed.

Lemma adjacency_matrix_bijective_vertex_count :
  forall n matrix g inf,
    gvalid g ->
    adjacency_matrix_model n matrix g inf ->
    Zlength (bijective_listV g) = n.
Proof.
  intros n matrix g inf Hg Hmodel.
  unfold adjacency_matrix_model in Hmodel.
  destruct Hmodel as [[Hrows _] [Hvertices _]].
  assert (Hn : 0 <= n).
  { rewrite <- Hrows. rewrite Zlength_correct. lia. }
  assert (Hperm : Permutation (bijective_listV g) (Zrange 0 n)).
  {
    apply NoDup_Permutation.
    - apply bijective_listV_NoDup; exact Hg.
    - apply NoDup_Zrange.
    - intros v.
      rewrite bijective_vertices by exact Hg.
      unfold vvalid, graph_instance.
      simpl.
      exact (Hvertices v).
  }
  apply Permutation_length in Hperm.
  assert (Hzlen :
    Zlength (bijective_listV g) = Zlength (Zrange 0 n)).
  {
    rewrite !Zlength_correct.
    f_equal.
    exact Hperm.
  }
  rewrite Hzlen.
  rewrite Zlength_Zrange by lia.
  lia.
Qed.

Lemma full_growing_subgraph_vertices_permutation :
  forall n matrix g inf s,
    adjacency_matrix_model n matrix g inf ->
    growing_subgraph_state g s ->
    state_vertex_count s = n ->
    Permutation (bijective_listV s.(Prim.graph_in_state)) (Zrange 0 n).
Proof.
  intros n matrix g inf s Hmodel Hgrow Hcount.
  destruct Hmodel as [[Hrows _] [Hvertices _]].
  destruct Hgrow as [Hg_s [_ [Hsub _]]].
  destruct Hsub as [Hsub_vertex _].
  assert (Hn_nonneg : 0 <= n).
  { rewrite <- Hrows. rewrite Zlength_correct. lia. }
  set (svs := bijective_listV s.(Prim.graph_in_state)).
  assert (Hsvs_nodup : NoDup svs).
  { subst svs. apply bijective_listV_NoDup. exact Hg_s. }
  assert (Hrange_nodup : NoDup (Zrange 0 n)).
  { apply NoDup_Zrange. }
  assert (Hsvs_len : length svs = length (Zrange 0 n)).
  {
    apply Nat2Z.inj.
    rewrite <- !Zlength_correct.
    subst svs.
    unfold state_vertex_count, vertex_num in Hcount.
    change (Zlength (bijective_listV (Prim.graph_in_state s)) =
            Zlength (Zrange 0 n)).
    rewrite Hcount.
    rewrite Zlength_Zrange by lia.
    lia.
  }
  assert (Hsvs_in_range : incl svs (Zrange 0 n)).
  {
    subst svs.
    intros v Hv.
    rewrite bijective_vertices in Hv by exact Hg_s.
    pose proof (Hsub_vertex v Hv) as Hv_g.
    unfold vvalid, graph_instance in Hv_g.
    simpl in Hv_g.
    apply Hvertices in Hv_g.
    exact Hv_g.
  }
  assert (Hrange_in_svs : incl (Zrange 0 n) svs).
  {
    intros v Hv.
    destruct (in_dec Z.eq_dec v svs) as [Hin | Hnotin]; [exact Hin|].
    exfalso.
    assert (Hcons_nodup : NoDup (v :: svs)).
    { constructor; auto. }
    assert (Hcons_incl : incl (v :: svs) (Zrange 0 n)).
    {
      intros x Hx.
      destruct Hx as [<- | Hx]; [exact Hv | apply Hsvs_in_range; exact Hx].
    }
    pose proof (NoDup_incl_length Hcons_nodup Hcons_incl) as Hlen.
    simpl in Hlen.
    rewrite Hsvs_len in Hlen.
    lia.
  }
  apply NoDup_Permutation; auto.
  intro v; split; [apply Hsvs_in_range | apply Hrange_in_svs].
Qed.

Lemma lowcost_prefix_sum_full_state :
  forall n matrix g inf s lowcost,
    adjacency_matrix_model n matrix g inf ->
    growing_subgraph_state g s ->
    state_vertex_count s = n ->
    lowcost_sum_matches_state s lowcost ->
    lowcost_prefix_sum n lowcost =
    graph_total_weight s.(Prim.graph_in_state).
Proof.
  intros n matrix g inf s lowcost Hmodel Hgrow Hcount Hsum.
  destruct Hsum as [Hsum _].
  rewrite <- Hsum.
  unfold lowcost_state_sum.
  erewrite lowcost_vertex_sum_perm.
  - reflexivity.
  - eapply full_growing_subgraph_vertices_permutation; eauto.
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
  destruct Hgrow as [_ [_ [Hsub _]]].
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

Lemma adjacency_matrix_outside_subgraph_state_vertex :
  forall n matrix g inf s,
    adjacency_matrix_model n matrix g inf ->
    gvalid s.(Prim.graph_in_state) ->
    subgraph2 s.(Prim.graph_in_state) g ->
    state_vertex_count s < n ->
    exists y,
      In y (graph_vertices g) /\
      ~ vvalid s.(Prim.graph_in_state) y.
Proof.
  intros n matrix g inf s Hmodel Hvalid_s Hsub Hlt.
  destruct Hmodel as [[Hrows _] [Hvertices _]].
  assert (Hn_nonneg : 0 <= n).
  { rewrite <- Hrows. rewrite Zlength_correct. lia. }
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
      Permutation (bijective_listV s.(Prim.graph_in_state)) (Zrange 0 n)).
    {
      apply NoDup_Permutation.
      - apply bijective_listV_NoDup. exact Hvalid_s.
      - apply NoDup_Zrange.
      - intros y.
        rewrite bijective_vertices by exact Hvalid_s.
        split.
        + intros Hy_s.
          pose proof (Hsub_vertex y Hy_s) as Hy_g.
          change (In y (graph_vertices g)) in Hy_g.
          apply Hvertices in Hy_g.
          exact Hy_g.
        + intros Hy_range.
          apply Hall_g_in_s.
          apply Hvertices.
          exact Hy_range.
    }
    apply Permutation_length in Hperm.
    assert (Hzlen :
      Zlength (bijective_listV s.(Prim.graph_in_state)) =
      Zlength (Zrange 0 n)).
    {
      rewrite !Zlength_correct.
      f_equal.
      exact Hperm.
    }
    unfold state_vertex_count, vertex_num in Hlt.
    rewrite Hzlen in Hlt.
    rewrite Zlength_Zrange in Hlt by lia.
    lia.
Qed.

Lemma has_cut_edge_exists_by_state_vertex_count :
  forall n matrix g inf s,
    adjacency_matrix_model n matrix g inf ->
    connected g ->
    growing_subgraph_state g s ->
    (exists x, vvalid s.(Prim.graph_in_state) x) ->
    state_vertex_count s < n ->
    exists e, Prim.is_cut_edge g s e.
Proof.
  intros n matrix g inf s Hmodel Hconn Hgrow [x Hx_s] Hlt.
  destruct Hgrow as [Hvalid_s [Hconn_s [Hsub Hweight_s]]].
  assert (Hgrow : growing_subgraph_state g s).
  { split; [exact Hvalid_s |].
    split; [exact Hconn_s |].
    split; [exact Hsub | exact Hweight_s]. }
  destruct (adjacency_matrix_outside_subgraph_state_vertex
    n matrix g inf s Hmodel Hvalid_s Hsub Hlt) as [y [Hy_g Hy_not_s]].
  eapply (reachable_crosses_outside_vertex g s x y); eauto.
Qed.

Lemma adjacency_matrix_model_edge :
  forall n matrix g inf u v,
    adjacency_matrix_model n matrix g inf ->
    0 <= u < n ->
    0 <= v < n ->
    matrix_entry matrix u v <> inf ->
    In (undirected_edge u v) (graph_edges g) /\
    graph_step g (undirected_edge u v) u v /\
    weight g (undirected_edge u v) = Some (matrix_entry matrix u v).
Proof.
  intros n matrix g inf u v Hmodel Hu Hv Hedge.
  unfold adjacency_matrix_model in Hmodel.
  destruct Hmodel as [_ [_ [_ [_ [_ Hcomplete]]]]].
  specialize (Hcomplete u v Hu Hv Hedge).
  destruct Hcomplete as [Hin [Hstep Hwt]].
  split; [exact Hin|].
  split; [exact Hstep|].
  unfold weight, edge_weight_instance; simpl.
  f_equal.
  exact Hwt.
Qed.

Lemma adjacency_matrix_model_default_edge_not_in_graph :
  forall n matrix g inf,
    adjacency_matrix_model n matrix g inf ->
    ~ In default_edge (graph_edges g).
Proof.
  intros n matrix g inf Hmodel Hin.
  unfold adjacency_matrix_model in Hmodel.
  destruct Hmodel as [_ [Hvertices [_ [Hwf _]]]].
  destruct (Hwf default_edge Hin) as [u [v Hstep]].
  unfold graph_step, edge_endpoints_valid, edge_src, edge_dst, default_edge in Hstep.
  simpl in Hstep.
  destruct Hstep as [_ [[Hsrc _] _]].
  apply Hvertices in Hsrc.
  rewrite <- In_Zrange in Hsrc.
  lia.
Qed.

Lemma prim_result_matrix_matches_from_parent_prefix :
  forall n input_matrix result_matrix g rg inf src s vertex_parent edge_parent,
    adjacency_matrix_model n input_matrix g inf ->
    growing_subgraph_state g s ->
    state_vertex_count s = n ->
    prim_state_graph_matches rg s ->
    selected_edges_match_state g src s edge_parent ->
    vertex_parent_matches_edge_parent g src vertex_parent edge_parent ->
    result_matrix_parent_prefix g src input_matrix result_matrix
      vertex_parent edge_parent inf n ->
    prim_result_matrix_matches result_matrix rg inf.
Proof.
  intros n input_matrix result_matrix g rg inf src s vertex_parent edge_parent
         Hmodel Hgrow Hcount Hrg Hselected Hparent Hprefix.
  unfold prim_result_matrix_matches.
  unfold prim_state_graph_matches in Hrg.
  subst rg.
  assert (Hstate_vertex_num :
    vertex_num s.(Prim.graph_in_state) = n).
  {
    unfold state_vertex_count in Hcount.
    exact Hcount.
  }
  rewrite Hstate_vertex_num.
  unfold result_matrix_parent_prefix in Hprefix.
  destruct Hprefix as [Hshape_result [_ Hcells]].
  pose proof Hcells as Hcells_all.
  pose proof Hmodel as Hmodel_full.
  pose proof Hgrow as Hgrow_full.
  unfold adjacency_matrix_model in Hmodel.
  destruct Hmodel as [Hshape_input [Hvertices [Hentry_bound [Hwf_g [Hedge_g _]]]]].
  destruct Hshape_input as [Hinput_len _].
  destruct Hgrow as [Hg_s [_ [Hsub_s Hweight_s]]].
  destruct Hselected as [Hsrc_valid [Hrange_s Hexact_s]].
  assert (Hperm :
    Permutation (bijective_listV s.(Prim.graph_in_state)) (Zrange 0 n)).
  {
    eapply full_growing_subgraph_vertices_permutation; eauto.
  }
  assert (Hvertex_s :
    forall v, In v (graph_vertices g) <-> vvalid s.(Prim.graph_in_state) v).
  {
    intro v.
    split.
    - intro Hv.
      apply (proj1 (bijective_vertices _ Hg_s v)).
      rewrite Hperm.
      apply Hvertices.
      exact Hv.
    - intro Hv.
      destruct Hsub_s as [Hsub_v _].
      exact (Hsub_v v Hv).
  }
  rewrite Hinput_len in Hshape_result.
  unfold adjacency_matrix_model.
  split; [exact Hshape_result|].
  split.
  { intro v.
    split.
    - intro Hv.
      pose proof (proj2 (bijective_vertices _ Hg_s v) Hv) as Hin.
      rewrite Hperm in Hin.
      exact Hin.
    - intro Hv.
      change (vvalid s.(Prim.graph_in_state) v).
      apply (proj1 (bijective_vertices _ Hg_s v)).
      rewrite Hperm.
      exact Hv. }
  split.
  - intros u v Hu Hv.
    assert (Hu_g : In u (graph_vertices g)).
    { apply Hvertices. rewrite <- In_Zrange. exact Hu. }
    assert (Hv_g : In v (graph_vertices g)).
    { apply Hvertices. rewrite <- In_Zrange. exact Hv. }
    specialize (Hcells u v Hu_g Hv_g).
    destruct Hcells as [[w [Hcell [Hres Hinput]]] | [_ Hres]].
    + right.
      rewrite Hres.
      specialize (Hentry_bound u v Hu Hv).
      rewrite Hinput in Hentry_bound.
      destruct Hentry_bound as [Heq | Hlt].
      * exfalso.
        unfold processed_parent_edge_cell in Hcell.
        destruct Hcell as [child [parent [e [_ [_ [_ [_ [_ [_ [_ [Hstep Hw]]]]]]]]]]].
        rewrite <- Hw in Heq.
        pose proof (step_evalid g e parent child Hstep) as Hevalid.
        specialize (Hedge_g e Hevalid).
        destruct Hedge_g as [_ [_ [_ Hnotinf]]].
        contradiction.
      * exact Hlt.
    + left. exact Hres.
  - split.
    + exact Hg_s.
    + split.
      * intros e He.
        assert (He_state : evalid s.(Prim.graph_in_state) e).
        { unfold evalid, graph_instance; simpl. exact He. }
        apply Hexact_s in He_state.
        destruct He_state as [child [Hchild_g [Hchild_src [Hchild_s Heq]]]].
        subst e.
        specialize (Hparent child Hchild_g) as [_ [_ [_ Hparent_child]]].
        specialize (Hrange_s child Hchild_g Hchild_src Hchild_s) as Hedge_in_g.
        destruct Hparent_child as [[_ He_default] | [Hp [Hpar_g [Hpar_child [Hcanon Hstep_g]]]]].
        { rewrite He_default in Hedge_in_g.
          exfalso.
          eapply adjacency_matrix_model_default_edge_not_in_graph; eauto. }
        assert (Hpar_range : 0 <= Znth child vertex_parent (-1) < n).
        { apply Hvertices in Hpar_g. rewrite <- In_Zrange in Hpar_g. exact Hpar_g. }
        assert (Hchild_range_n : 0 <= child < n).
        { apply Hvertices in Hchild_g. rewrite <- In_Zrange in Hchild_g. exact Hchild_g. }
        assert (Hsrc_range : 0 <= fst (undirected_edge (Znth child vertex_parent (-1)) child) < n).
        {
          destruct (undirected_edge_connects (Znth child vertex_parent (-1)) child)
            as [[Hfst _] | [Hfst _]];
            rewrite Hfst; assumption.
        }
        assert (Hdst_range : 0 <= snd (undirected_edge (Znth child vertex_parent (-1)) child) < n).
        {
          destruct (undirected_edge_connects (Znth child vertex_parent (-1)) child)
            as [[_ Hsnd] | [_ Hsnd]];
            rewrite Hsnd; assumption.
        }
        split.
        { unfold matrix_index_valid, edge_src, edge_dst.
          rewrite Hcanon.
          split; [exact Hsrc_range | exact Hdst_range]. }
        assert (Hfst_g : In (fst (undirected_edge (Znth child vertex_parent (-1)) child)) (graph_vertices g)).
        { apply Hvertices. rewrite <- In_Zrange. exact Hsrc_range. }
        assert (Hsnd_g : In (snd (undirected_edge (Znth child vertex_parent (-1)) child)) (graph_vertices g)).
        { apply Hvertices. rewrite <- In_Zrange. exact Hdst_range. }
        specialize (Hcells (fst (undirected_edge (Znth child vertex_parent (-1)) child))
                           (snd (undirected_edge (Znth child vertex_parent (-1)) child))
                           Hfst_g Hsnd_g).
        assert (Hcell :
          processed_parent_edge_cell g vertex_parent edge_parent n
            (fst (undirected_edge (Znth child vertex_parent (-1)) child))
            (snd (undirected_edge (Znth child vertex_parent (-1)) child))
            (graph_weight g (undirected_edge (Znth child vertex_parent (-1)) child))).
        {
          exists child, (Znth child vertex_parent (-1)),
            (undirected_edge (Znth child vertex_parent (-1)) child).
          split.
          - rewrite <- In_Zrange. exact Hchild_range_n.
          - split; [exact Hchild_g|].
            split; [reflexivity|].
            split; [exact Hp|].
            split; [symmetry; exact Hcanon|].
            split; [reflexivity|].
            split; [apply undirected_edge_idempotent|].
            split.
            + rewrite Hcanon in Hstep_g. exact Hstep_g.
            + reflexivity.
        }
        destruct Hcells as [[w [Hcell' [Hres Hinput]]] | [Hnone _]].
        -- unfold processed_parent_edge_cell in Hcell'.
           destruct Hcell' as [child' [parent' [e' [_ [_ [_ [_ [_ [_ [Hcanon_uv' [_ Hw]]]]]]]]]]].
           rewrite Hcanon.
           unfold edge_src, edge_dst; simpl.
           assert (Hnotinf : graph_weight g (undirected_edge (Znth child vertex_parent (-1)) child) <> inf).
           {
             specialize (Hedge_g (Znth child edge_parent default_edge) Hedge_in_g).
             destruct Hedge_g as [_ [_ [_ Hnotinf]]].
             rewrite Hcanon in Hnotinf.
             exact Hnotinf.
           }
           assert (Hcells_rev :=
             Hcells_all (snd (undirected_edge (Znth child vertex_parent (-1)) child))
                    (fst (undirected_edge (Znth child vertex_parent (-1)) child))
                    Hsnd_g Hfst_g).
           assert (Hcell_rev :
             processed_parent_edge_cell g vertex_parent edge_parent n
               (snd (undirected_edge (Znth child vertex_parent (-1)) child))
               (fst (undirected_edge (Znth child vertex_parent (-1)) child))
               (graph_weight g (undirected_edge (Znth child vertex_parent (-1)) child))).
           {
             exists child, (Znth child vertex_parent (-1)),
               (undirected_edge (Znth child vertex_parent (-1)) child).
             split.
             - rewrite <- In_Zrange. exact Hchild_range_n.
             - split; [exact Hchild_g|].
               split; [reflexivity|].
               split; [exact Hp|].
               split; [symmetry; exact Hcanon|].
               split; [reflexivity|].
               split.
               + rewrite undirected_edge_comm. apply undirected_edge_idempotent.
               + split.
                 * rewrite Hcanon in Hstep_g. exact Hstep_g.
                 * reflexivity.
           }
           destruct Hcells_rev as [[w' [Hcell_rev' [Hres_rev _]]] | [Hnone_rev _]].
           ++ unfold processed_parent_edge_cell in Hcell_rev'.
              destruct Hcell_rev' as [child'' [parent'' [e'' [_ [_ [_ [_ [_ [_ [Hcanon_uv_rev' [_ Hw_rev]]]]]]]]]]].
              rewrite undirected_edge_idempotent in Hcanon_uv'.
              rewrite undirected_edge_comm in Hcanon_uv_rev'.
              rewrite undirected_edge_idempotent in Hcanon_uv_rev'.
              subst e' e''.
              repeat split.
              ** rewrite Hres, <- Hw, Hweight_s. reflexivity.
              ** rewrite Hres_rev, <- Hw_rev, Hweight_s. reflexivity.
              ** intro Hbad. apply Hnotinf. rewrite <- Hweight_s. exact Hbad.
           ++ exfalso.
              apply (Hnone_rev (graph_weight g (undirected_edge (Znth child vertex_parent (-1)) child))).
              exact Hcell_rev.
        -- exfalso. apply (Hnone (graph_weight g (undirected_edge (Znth child vertex_parent (-1)) child))).
           exact Hcell.
      * intros u v Hu Hv Hres_not_inf.
        assert (Hu_g : In u (graph_vertices g)).
        { apply Hvertices. rewrite <- In_Zrange. exact Hu. }
        assert (Hv_g : In v (graph_vertices g)).
        { apply Hvertices. rewrite <- In_Zrange. exact Hv. }
        specialize (Hcells u v Hu_g Hv_g).
        destruct Hcells as [[w [Hcell [Hres _]]] | [_ Hres]].
        -- unfold processed_parent_edge_cell in Hcell.
           destruct Hcell as [child [parent [e Hcell]]].
           destruct Hcell as [_ [Hchild_g [Hparent_eq [Hparent_not_none
             [Heq_edge [Hcanon_parent [Hcanon_uv [_ Hw]]]]]]]].
           assert (Hchild_s : vvalid s.(Prim.graph_in_state) child).
           { apply Hvertex_s. exact Hchild_g. }
           assert (Hchild_src : child <> src).
           {
             intro Hcs.
             specialize (Hparent child Hchild_g) as [_ [_ [Hsrc_empty _]]].
             specialize (Hsrc_empty Hcs).
             rewrite <- Hparent_eq in Hsrc_empty.
             destruct Hsrc_empty as [Hbad _].
             contradiction.
           }
           assert (He_state : evalid s.(Prim.graph_in_state) (undirected_edge u v)).
           {
             rewrite Hcanon_uv.
             apply Hexact_s.
             exists child.
             split; [exact Hchild_g|].
             split; [exact Hchild_src|].
             split; [exact Hchild_s|].
             exact Heq_edge.
           }
           split.
           ++ unfold evalid, graph_instance in He_state; simpl in He_state.
              exact He_state.
           ++ split.
              ** unfold graph_step, edge_endpoints_valid, edge_src, edge_dst.
                 split.
                 { unfold evalid, graph_instance in He_state; simpl in He_state.
                   exact He_state. }
                 split.
                 {
                   destruct (undirected_edge_connects u v) as [[Hfst Hsnd] | [Hfst Hsnd]];
                     split; rewrite Hfst || rewrite Hsnd; apply Hvertex_s;
                     [exact Hu_g | exact Hv_g | exact Hv_g | exact Hu_g].
                 }
                 unfold undirected_edge.
                 destruct (Z.leb_spec0 u v); simpl; auto.
              ** rewrite Hres.
                 rewrite <- Hw.
                 rewrite <- Hweight_s.
                 rewrite Hcanon_uv.
                 reflexivity.
        -- contradiction.
Qed.

Lemma initSt_visited_matches_state_zero_repeat :
  forall n matrix g inf src,
    adjacency_matrix_model n matrix g inf ->
    src = 0 ->
    visited_matches_state g (initSt g src)
      (replace_Znth src 1 (repeat 0 (Z.to_nat n))).
Proof.
  intros n matrix g inf src Hmodel Hsrc.
  unfold visited_matches_state.
  intros v Hv_graph.
  assert (Hv_range : 0 <= v < n).
 {
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [_ [Hvertices _]].
    apply Hvertices in Hv_graph.
    rewrite <- In_Zrange in Hv_graph.
    exact Hv_graph.
  }
  assert (Hlen : Zlength (repeat 0 (Z.to_nat n)) = n).
  {
    rewrite Zlength_correct, repeat_length.
    lia.
  }
  rewrite initSt_vvalid.
  subst src.
  split.
  - intros Hnz.
    destruct (Z.eq_dec v 0) as [Hv0 | Hv0]; [exact Hv0|].
    exfalso.
    rewrite (Znth_replace_Znth_diff_local
      (repeat 0 (Z.to_nat n)) 0 v 1) in Hnz.
    + rewrite Znth_repeat_lt in Hnz by lia.
      contradiction.
    + rewrite Hlen; lia.
    + rewrite Hlen; lia.
    + lia.
  - intros Hv0.
    subst v.
    rewrite Znth_replace_Znth_same_local; [lia |].
    rewrite Hlen; lia.
Qed.

(** ** lowcost 和 ghost edge_parent 与当前 Prim 状态的关系

    邻接矩阵 C 程序只真实保存 [lowcost]。这里额外维护一个 ghost
    [edge_parent] 列表：对尚未加入生长子图的点 [v]，
    [edge_parent[v]] 记录实现 [lowcost[v]] 的那条规范无向边。
 *)

Definition is_cut_edge_to_vertex (g : G) (s : St) (v : V) (e : E) : Prop :=
  ~ vvalid s.(Prim.graph_in_state) v /\
  (edge_src g e = v \/ edge_dst g e = v) /\
  Prim.is_cut_edge g s e.

Definition is_min_cut_edge_to_vertex (g : G) (s : St) (v : V) (e : E) : Prop :=
  min_object_of_subset Z_op_le
    (fun e => is_cut_edge_to_vertex g s v e)
    (weight g)
    e.

Definition vertex_has_parent_edge
    (g : G) (s : St) (lowcost : list Z) (edge_parent : list E) (inf : Z) (v : V) : Prop :=
  let e := Znth v edge_parent default_edge in
  In e (graph_edges g) /\
  Znth v lowcost 0 < inf /\
  is_min_cut_edge_to_vertex g s v e /\
  weight g e = Some (Znth v lowcost 0).

Definition lowcost_parent_match
    (g : G) (s : St) (lowcost : list Z) (edge_parent : list E) (inf : Z) : Prop :=
  (forall v,
     In v (graph_vertices g) ->
     0 <= v < Zlength lowcost /\ 0 <= v < Zlength edge_parent) /\
  forall v,
    In v (graph_vertices g) ->
    ~ vvalid s.(Prim.graph_in_state) v ->
    (vertex_has_parent_edge g s lowcost edge_parent inf v \/
		     ((forall e, ~ is_cut_edge_to_vertex g s v e) /\
		      Znth v lowcost 0 = inf)).

Lemma lowcost_parent_match_unvisited_nonneg :
  forall n matrix g s lowcost edge_parent visited inf v,
    adjacency_matrix_model n matrix g inf ->
    0 <= inf ->
    0 <= v < n ->
    visited_matches_state g s visited ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    Znth v visited 0 = 0 ->
    0 <= Znth v lowcost 0.
Proof.
  intros n matrix g s lowcost edge_parent visited inf v
         Hmodel Hinf Hv_range Hvisited Hmatch Hvisited0.
  assert (Hv_graph : In v (graph_vertices g)).
  {
    eapply adjacency_matrix_vertex_in_graph; eauto.
  }
  assert (Hv_not_valid : ~ vvalid s.(Prim.graph_in_state) v).
  {
    specialize (Hvisited v Hv_graph).
    intros Hv_valid.
    apply (proj2 Hvisited) in Hv_valid.
    rewrite Hvisited0 in Hv_valid.
    contradiction.
  }
  unfold lowcost_parent_match in Hmatch.
  destruct Hmatch as [_ Hbody].
  specialize (Hbody v Hv_graph Hv_not_valid).
  destruct Hbody as [Hparent | [_ Hnone]].
  - unfold vertex_has_parent_edge in Hparent.
    destruct Hparent as [Hin [_ [_ Hweight]]].
    unfold weight, edge_weight_instance in Hweight; simpl in Hweight.
    inversion Hweight; subst; clear Hweight.
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [_ [_ [Hentry [_ [Hedge _]]]]].
    specialize (Hedge (Znth v edge_parent default_edge) Hin).
    destruct Hedge as [[Hsrc_range Hdst_range] [Hweight_src [_ Hnot_inf]]].
    rewrite Hweight_src.
    specialize (Hentry
      (edge_src g (Znth v edge_parent default_edge))
      (edge_dst g (Znth v edge_parent default_edge))
      Hsrc_range Hdst_range).
    destruct Hentry as [Hentry_inf | [Hentry_nonneg _]].
    + exfalso.
      apply Hnot_inf.
      rewrite Hweight_src.
      exact Hentry_inf.
    + exact Hentry_nonneg.
  - rewrite Hnone.
    exact Hinf.
Qed.

Definition vertex_has_parent_edge_by
    (g : G) (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list E) (inf : Z) (v : V) : Prop :=
  let e := Znth v edge_parent default_edge in
  In e (graph_edges g) /\
  Znth v lowcost 0 < inf /\
  min_object_of_subset Z_op_le
    (edge_for_vertex v)
    (weight g)
    e /\
  weight g e = Some (Znth v lowcost 0).

Definition lowcost_parent_match_by
    (g : G)
    (eligible_vertex : V -> Prop)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list E)
    (inf : Z) : Prop :=
  (forall v,
     In v (graph_vertices g) ->
     0 <= v < Zlength lowcost /\ 0 <= v < Zlength edge_parent) /\
  forall v,
    In v (graph_vertices g) ->
    eligible_vertex v ->
    (vertex_has_parent_edge_by g edge_for_vertex lowcost edge_parent inf v \/
     ((forall e, ~ edge_for_vertex v e) /\
      Znth v lowcost 0 = inf)).

Lemma lowcost_parent_match_to_by :
  forall g s lowcost edge_parent inf,
    lowcost_parent_match g s lowcost edge_parent inf ->
    lowcost_parent_match_by
      g
      (fun v => ~ vvalid s.(Prim.graph_in_state) v)
      (fun v e => is_cut_edge_to_vertex g s v e)
      lowcost edge_parent inf.
Proof.
  intros g s lowcost edge_parent inf Hmatch.
  unfold lowcost_parent_match_by, lowcost_parent_match in *.
  destruct Hmatch as [Hrange Hbody].
  split; [exact Hrange|].
  intros v Hv Helig.
  specialize (Hbody v Hv Helig).
  destruct Hbody as [Hparent | Hnone].
  - left.
    unfold vertex_has_parent_edge_by, vertex_has_parent_edge in *.
    exact Hparent.
  - right; exact Hnone.
Qed.

Lemma lowcost_parent_match_by_to :
  forall g s lowcost edge_parent inf,
    lowcost_parent_match_by
      g
      (fun v => ~ vvalid s.(Prim.graph_in_state) v)
      (fun v e => is_cut_edge_to_vertex g s v e)
      lowcost edge_parent inf ->
    lowcost_parent_match g s lowcost edge_parent inf.
Proof.
  intros g s lowcost edge_parent inf Hmatch.
  unfold lowcost_parent_match_by, lowcost_parent_match in *.
  destruct Hmatch as [Hrange Hbody].
  split; [exact Hrange|].
  intros v Hv Helig.
  specialize (Hbody v Hv Helig).
  destruct Hbody as [Hparent | Hnone].
  - left.
    unfold vertex_has_parent_edge_by, vertex_has_parent_edge in *.
    exact Hparent.
  - right; exact Hnone.
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
         Hmatch Helig Hedge.
  unfold lowcost_parent_match_by in *.
  destruct Hmatch as [Hrange Hbody].
  split; [exact Hrange|].
  intros v Hv Helig2.
  specialize (Hbody v Hv (Helig v Hv Helig2)).
  destruct Hbody as [Hparent | Hnone].
  - left.
    unfold vertex_has_parent_edge_by in *.
    destruct Hparent as [Hin [Hlow [Hmin Hweight]]].
    split; [exact Hin|].
    split; [exact Hlow|].
    split; [| exact Hweight].
    unfold min_object_of_subset in *.
    destruct Hmin as [Hedge_old Hmin].
    split.
    + apply (Hedge v (Znth v edge_parent default_edge) Hv Helig2).
      exact Hedge_old.
    + intros e Hedge_new.
      apply Hmin.
      apply (Hedge v e Hv Helig2).
      exact Hedge_new.
  - right.
    destruct Hnone as [Hnone Hlow].
    split; [| exact Hlow].
    intros e Hedge_new.
    exact (Hnone e ((proj2 (Hedge v e Hv Helig2)) Hedge_new)).
Qed.

Definition candidate_vertex
    (g : G) (s : St) (lowcost : list Z) (edge_parent : list E) (inf : Z) (v : V) : Prop :=
  In v (graph_vertices g) /\
  ~ vvalid s.(Prim.graph_in_state) v /\
  vertex_has_parent_edge g s lowcost edge_parent inf v.

Definition candidate_vertex_exists_in_range
    (n : Z) (g : G) (s : St) (lowcost : list Z) (edge_parent : list E) (inf : Z) : Prop :=
  exists v,
    In v (Zrange 0 n) /\
    candidate_vertex g s lowcost edge_parent inf v.

Definition min_vertex_in_range
    (g : G) (s : St) (j : Z) (inf : Z)
    (minIndex : V) (lowcost : list Z) (edge_parent : list E) : Prop :=
  (minIndex = -1 /\
   forall v,
     In v (Zrange 0 j) ->
     ~ candidate_vertex g s lowcost edge_parent inf v) \/
  (candidate_vertex g s lowcost edge_parent inf minIndex /\
   In minIndex (Zrange 0 j) /\
   forall v,
     In v (Zrange 0 j) ->
     candidate_vertex g s lowcost edge_parent inf v ->
     Znth minIndex lowcost 0 <= Znth v lowcost 0).

Definition selected_parent_edge_is_min_cut_edge
    (g : G) (s : St) (edge_parent : list E) (minIndex : V) : Prop :=
  min_object_of_subset Z_op_le
    (fun e => Prim.is_cut_edge g s e)
    (weight g)
    (Znth minIndex edge_parent default_edge).

Definition selected_parent_pair
    (g : G) (s : St) (edge_parent : list E) (minIndex u v : V) : Prop :=
  let e := Znth minIndex edge_parent default_edge in
  v = minIndex /\
  vvalid s.(Prim.graph_in_state) u /\
  ~ vvalid s.(Prim.graph_in_state) v /\
  step_aux g e u v.

Lemma selected_parent_lowcost_bounds :
  forall n matrix g s lowcost edge_parent inf minIndex u v,
    adjacency_matrix_model n matrix g inf ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    selected_parent_pair g s edge_parent minIndex u v ->
    0 <= minIndex < n ->
    0 <= Znth minIndex lowcost 0 /\ Znth minIndex lowcost 0 < inf.
Proof.
  intros n matrix g s lowcost edge_parent inf minIndex u v
         Hmodel Hmatch Hpair Hrange.
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [-> [Hu [Hvout Hstep]]].
  assert (Hv_graph : In minIndex (graph_vertices g)).
  {
    eapply adjacency_matrix_vertex_in_graph; eauto.
  }
  unfold lowcost_parent_match in Hmatch.
  destruct Hmatch as [_ Hbody].
  specialize (Hbody minIndex Hv_graph Hvout).
  destruct Hbody as [Hparent | [Hnone _]].
  - unfold vertex_has_parent_edge in Hparent.
    destruct Hparent as [Hin [Hlt [_ Hweight]]].
    split; [| exact Hlt].
    unfold weight, edge_weight_instance in Hweight; simpl in Hweight.
    inversion Hweight; subst; clear Hweight.
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [_ [_ [Hentry [_ [Hedge _]]]]].
    specialize (Hedge (Znth minIndex edge_parent default_edge) Hin).
    destruct Hedge as [[Hsrc_range Hdst_range] [Hweight_src [_ Hnot_inf]]].
    rewrite Hweight_src.
    specialize (Hentry
      (edge_src g (Znth minIndex edge_parent default_edge))
      (edge_dst g (Znth minIndex edge_parent default_edge))
      Hsrc_range Hdst_range).
    destruct Hentry as [Hentry_inf | [Hentry_nonneg _]].
    + exfalso.
      apply Hnot_inf.
      rewrite Hweight_src.
      exact Hentry_inf.
    + exact Hentry_nonneg.
  - exfalso.
    apply (Hnone (Znth minIndex edge_parent default_edge)).
    unfold is_cut_edge_to_vertex.
    split; [exact Hvout |].
    split.
    + unfold step_aux, graph_instance, graph_step in Hstep.
      destruct Hstep as [_ [_ [[_ Hdst] | [_ Hsrc]]]].
      * right. symmetry. exact Hdst.
      * left. symmetry. exact Hsrc.
    + exists u, minIndex.
      split; [exact Hu |].
      split; [exact Hvout | exact Hstep].
Qed.

Definition selected_parent_add_to_mst
    (g : G) (s s_next : St) (edge_parent : list E) (minIndex : V) : Prop :=
  exists u v,
    selected_parent_pair g s edge_parent minIndex u v /\
    addEdge s.(Prim.graph_in_state) s_next.(Prim.graph_in_state)
      u v (Znth minIndex edge_parent default_edge) /\
    s_next.(Prim.graph_in_state) =
      add_edge_graph s.(Prim.graph_in_state) u v
        (Znth minIndex edge_parent default_edge).

Lemma selected_parent_add_to_mst_vvalid :
  forall g s s_next edge_parent minIndex x,
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    vvalid s_next.(Prim.graph_in_state) x <->
      vvalid s.(Prim.graph_in_state) x \/ x = minIndex.
Proof.
  intros g s s_next edge_parent minIndex x Hadd.
  destruct Hadd as [u [v [Hpair [Hadd _]]]].
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [-> [Hu [_ _]]].
  rewrite (addEdge_vvalid _ _ _ _ _ Hadd x).
  split.
  - intros [Hx | [Hx | Hx]]; subst; auto.
  - intros [Hx | Hx]; subst; auto.
Qed.

Lemma selected_parent_add_to_mst_old_vvalid :
  forall g s s_next edge_parent minIndex x,
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    vvalid s.(Prim.graph_in_state) x ->
    vvalid s_next.(Prim.graph_in_state) x.
Proof.
  intros g s s_next edge_parent minIndex x Hadd Hx.
  rewrite (selected_parent_add_to_mst_vvalid
    g s s_next edge_parent minIndex x Hadd).
  left; exact Hx.
Qed.

Lemma selected_parent_add_to_mst_minIndex_vvalid :
  forall g s s_next edge_parent minIndex,
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    vvalid s_next.(Prim.graph_in_state) minIndex.
Proof.
  intros g s s_next edge_parent minIndex Hadd.
  rewrite (selected_parent_add_to_mst_vvalid
    g s s_next edge_parent minIndex minIndex Hadd).
  right; reflexivity.
Qed.

Lemma selected_parent_add_to_mst_still_outside :
  forall g s s_next edge_parent minIndex x,
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    ~ vvalid s.(Prim.graph_in_state) x ->
    x <> minIndex ->
    ~ vvalid s_next.(Prim.graph_in_state) x.
Proof.
  intros g s s_next edge_parent minIndex x Hadd Hx Hneq.
  rewrite (selected_parent_add_to_mst_vvalid
    g s s_next edge_parent minIndex x Hadd).
  intros [Hold | Hnew]; [apply Hx; exact Hold | apply Hneq; exact Hnew].
Qed.

Lemma selected_parent_edge_not_evalid_in_state :
  forall g s edge_parent minIndex u v,
    gvalid g ->
    growing_subgraph_state g s ->
    selected_parent_pair g s edge_parent minIndex u v ->
    ~ evalid s.(Prim.graph_in_state)
        (Znth minIndex edge_parent default_edge).
Proof.
  intros g s edge_parent minIndex u v Hg Hstate Hpair Heold.
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [-> [Hu [Hvout Hstep_g]]].
  destruct Hstate as [Hsvalid [_ [Hsub _]]].
  destruct (no_empty_edge s.(Prim.graph_in_state)
    (Znth minIndex edge_parent default_edge) Hsvalid Heold)
    as [x [y Hstep_old]].
  pose proof (subgraph2_step_aux _ _ Hsub x y
    (Znth minIndex edge_parent default_edge) Hstep_old) as Hstep_g_old.
  pose proof (step_aux_unique_undirected g
    (Znth minIndex edge_parent default_edge) u minIndex x y
    Hg Hstep_g Hstep_g_old)
    as [[Hx Hy] | [Hx Hy]]; subst.
  - apply Hvout. eapply step_vvalid2; eauto.
  - apply Hvout. eapply step_vvalid1; eauto.
Qed.

Lemma selected_parent_add_to_mst_exists :
  forall g src s edge_parent minIndex u v,
    PrimEnv g src ->
    growing_subgraph_state g s ->
    selected_parent_pair g s edge_parent minIndex u v ->
    exists s_next,
      selected_parent_add_to_mst g s s_next edge_parent minIndex.
Proof.
  intros g src s edge_parent minIndex u v Henv Hstate Hpair.
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [-> [Hu [Hvout Hstep]]].
  pose proof Hstate as Hstate_full.
  destruct Hstate as [Hsvalid [_ [Hsub _]]].
  assert (Hnotin :
    ~ evalid s.(Prim.graph_in_state)
        (Znth minIndex edge_parent default_edge)).
  {
    eapply selected_parent_edge_not_evalid_in_state
      with (g := g) (s := s) (edge_parent := edge_parent)
           (minIndex := minIndex) (u := u) (v := minIndex).
    - exact (prim_graph_valid g src Henv).
    - exact Hstate_full.
    - unfold selected_parent_pair.
      split; [reflexivity|].
      split; [exact Hu|].
      split; [exact Hvout|].
      exact Hstep.
  }
  exists (@Prim.mkSt_s G
    (add_edge_graph s.(Prim.graph_in_state) u minIndex
      (Znth minIndex edge_parent default_edge))).
  exists u, minIndex.
  split.
  - unfold selected_parent_pair.
    split; [reflexivity|].
    split; [exact Hu|].
    split; [exact Hvout|].
    exact Hstep.
  - simpl.
    split.
    + apply add_edge_graph_addEdge.
      * exact Hsvalid.
      * exact Hu.
      * exact Hnotin.
      * eapply graph_step_edge_connects; exact Hstep.
    + reflexivity.
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
  forall g s s_next edge_parent minIndex,
    growing_subgraph_state g s ->
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    growing_subgraph_state g s_next.
Proof.
  intros g s s_next edge_parent minIndex Hstate Hadd.
  destruct Hstate as [Hsvalid [Hconn [Hsub Hweight_s]]].
  destruct Hadd as [u [v [Hpair [HaddEdge Hnext_eq]]]].
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [-> [Hu [Hvout Hstep_g]]].
  assert (Hsnextvalid : gvalid s_next.(Prim.graph_in_state)).
  { eapply addEdge_gvalid; eauto. }
  split.
  - exact Hsnextvalid.
  - split.
    + eapply (addEdge_connected_preserve
        s.(Prim.graph_in_state) s_next.(Prim.graph_in_state)
        u minIndex (Znth minIndex edge_parent default_edge));
        eauto.
	    + split.
	      * constructor.
	        -- intros x Hx.
	           destruct HaddEdge as [Hadd_vvalid _ _].
	           apply Hadd_vvalid in Hx as [Hx | [Hx | Hx]].
	           ++ exact (subgraph2_vertex _ _ Hsub x Hx).
	           ++ subst x. exact (step_vvalid1 g (Znth minIndex edge_parent default_edge) u minIndex Hstep_g).
	           ++ subst x. exact (step_vvalid2 g (Znth minIndex edge_parent default_edge) u minIndex Hstep_g).
	        -- intros x y e Hxy.
	           destruct HaddEdge as [_ _ Hadd_step].
	           apply Hadd_step in Hxy as [Hxy_old | [Heq Hxy_new]].
	           ++ exact (subgraph2_step_aux _ _ Hsub x y e Hxy_old).
	           ++ subst e.
	              destruct Hxy_new as [[-> ->] | [-> ->]].
	              ** exact Hstep_g.
	              ** apply step_sym. exact Hstep_g.
	      * intros e.
	        rewrite Hnext_eq.
	        unfold add_edge_graph; simpl.
	        exact (Hweight_s e).
Qed.

Lemma selected_parent_add_to_mst_state_vertex_count :
  forall g s s_next edge_parent minIndex,
    growing_subgraph_state g s ->
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    state_vertex_count s_next = state_vertex_count s + 1.
Proof.
  intros g s s_next edge_parent minIndex Hstate Hadd.
  pose proof Hstate as Hstate_full.
  destruct Hstate as [Hsvalid [_ _]].
  pose proof (selected_parent_add_to_mst_growing
    g s s_next edge_parent minIndex Hstate_full Hadd) as Hgrow_next.
  destruct Hgrow_next as [Hsnextvalid _].
  destruct Hadd as [u [v [Hpair [HaddEdge _]]]].
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [-> [Hu [Hvout _]]].
  assert (Hperm :
    Permutation
      (bijective_listV s_next.(Prim.graph_in_state))
      (minIndex :: bijective_listV s.(Prim.graph_in_state))).
  {
    apply NoDup_Permutation.
    - apply bijective_listV_NoDup; exact Hsnextvalid.
    - constructor.
      + rewrite bijective_vertices by exact Hsvalid.
        exact Hvout.
      + apply bijective_listV_NoDup; exact Hsvalid.
    - intros x.
      rewrite bijective_vertices by exact Hsnextvalid.
      rewrite (addEdge_vvalid _ _ _ _ _ HaddEdge x).
      simpl.
      rewrite bijective_vertices by exact Hsvalid.
      split.
      + intros [Hx | [Hx | Hx]].
        * right; exact Hx.
        * subst x; right; exact Hu.
        * subst x; left; reflexivity.
      + intros [Hx | Hx].
        * subst x; right; right; reflexivity.
        * left; exact Hx.
  }
  unfold state_vertex_count, vertex_num.
  apply Permutation_length in Hperm.
  rewrite !Zlength_correct.
  rewrite Hperm.
  simpl.
  lia.
Qed.

Lemma selected_parent_add_to_mst_vertex_perm :
  forall g s s_next edge_parent minIndex,
    growing_subgraph_state g s ->
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    Permutation
      (bijective_listV s_next.(Prim.graph_in_state))
      (minIndex :: bijective_listV s.(Prim.graph_in_state)).
Proof.
  intros g s s_next edge_parent minIndex Hstate Hadd.
  pose proof Hstate as Hstate_full.
  destruct Hstate as [Hsvalid [_ _]].
  pose proof (selected_parent_add_to_mst_growing
    g s s_next edge_parent minIndex Hstate_full Hadd) as Hgrow_next.
  destruct Hgrow_next as [Hsnextvalid _].
  destruct Hadd as [u [v [Hpair [HaddEdge _]]]].
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [-> [Hu [Hvout _]]].
  apply NoDup_Permutation.
  - apply bijective_listV_NoDup; exact Hsnextvalid.
  - constructor.
    + rewrite bijective_vertices by exact Hsvalid.
      exact Hvout.
    + apply bijective_listV_NoDup; exact Hsvalid.
  - intros x.
    rewrite bijective_vertices by exact Hsnextvalid.
    rewrite (addEdge_vvalid _ _ _ _ _ HaddEdge x).
    simpl.
    rewrite bijective_vertices by exact Hsvalid.
    split.
    + intros [Hx | [Hx | Hx]].
      * right; exact Hx.
      * subst x; right; exact Hu.
      * subst x; left; reflexivity.
    + intros [Hx | Hx].
      * subst x; right; right; reflexivity.
      * left; exact Hx.
Qed.

Lemma selected_parent_add_to_mst_lowcost_sum_matches_state :
  forall g s s_next lowcost edge_parent inf minIndex,
    PrimEnv g 0 ->
    growing_subgraph_state g s ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    lowcost_sum_matches_state s lowcost ->
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    lowcost_sum_matches_state s_next lowcost.
Proof.
  intros g s s_next lowcost edge_parent inf minIndex
         Henv Hstate Hmatch Hsum Hadd.
  destruct Hsum as [Hsum_eq Hsum_bound].
  split; [| exact Hsum_bound].
  pose proof Hstate as Hstate_full.
  destruct Hstate as [Hsvalid [_ [_ Hweight_s]]].
  pose proof Hadd as Hadd_full.
  destruct Hadd as [u [v [Hpair [HaddEdge Hnext_eq]]]].
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [-> [Hu [Hvout Hstep]]].
  set (e := Znth minIndex edge_parent default_edge).
  assert (Hmin_graph : In minIndex (graph_vertices g)).
  { change (vvalid g minIndex). eapply step_vvalid2; eauto. }
  assert (Hweight_low : graph_weight g e = Znth minIndex lowcost 0).
  {
    unfold lowcost_parent_match in Hmatch.
    destruct Hmatch as [_ Hbody].
    specialize (Hbody minIndex Hmin_graph Hvout).
    destruct Hbody as [Hparent | [Hnone _]].
    - unfold vertex_has_parent_edge in Hparent.
      fold e in Hparent.
      destruct Hparent as [_ [_ [_ Hweight]]].
      unfold weight, edge_weight_instance in Hweight; simpl in Hweight.
      inversion Hweight; reflexivity.
    - exfalso.
      apply (Hnone e).
      unfold is_cut_edge_to_vertex.
      split; [exact Hvout|].
      split.
      + unfold step_aux, graph_instance, graph_step in Hstep.
        destruct Hstep as [_ [_ [[_ Hdst] | [_ Hsrc]]]].
        * right. symmetry. exact Hdst.
        * left. symmetry. exact Hsrc.
      + exists u, minIndex.
        split; [exact Hu|].
        split; [exact Hvout|].
        exact Hstep.
  }
  assert (Hnotin : ~ evalid s.(Prim.graph_in_state) e).
  {
    subst e.
    eapply selected_parent_edge_not_evalid_in_state
      with (g := g) (s := s) (edge_parent := edge_parent)
           (minIndex := minIndex) (u := u) (v := minIndex).
    - exact (prim_graph_valid g 0 Henv).
    - exact Hstate_full.
    - unfold selected_parent_pair.
      split; [reflexivity|].
      split; [exact Hu|].
      split; [exact Hvout|].
      exact Hstep.
  }
  assert (Hperm :
    Permutation
      (bijective_listV s_next.(Prim.graph_in_state))
      (minIndex :: bijective_listV s.(Prim.graph_in_state))).
  {
    eapply selected_parent_add_to_mst_vertex_perm; eauto.
  }
  unfold lowcost_state_sum in *.
  rewrite (lowcost_vertex_sum_perm
    (bijective_listV s_next.(Prim.graph_in_state))
    (minIndex :: bijective_listV s.(Prim.graph_in_state))
    lowcost Hperm).
  unfold lowcost_vertex_sum at 1.
  simpl.
  change (fold_right Z.add 0
    (map (fun v : Z => Znth v lowcost 0)
      (bijective_listV (Prim.graph_in_state s))))
    with (lowcost_vertex_sum
      (bijective_listV (Prim.graph_in_state s)) lowcost).
  rewrite Hsum_eq.
  rewrite Hnext_eq.
  rewrite graph_total_weight_add_edge_graph by exact Hnotin.
  rewrite Hweight_s.
  change (graph_weight g (Znth minIndex edge_parent default_edge))
    with (graph_weight g e).
  rewrite Hweight_low.
  lia.
Qed.

Lemma selected_parent_add_to_mst_visited_matches :
  forall n matrix g inf s s_next edge_parent minIndex visited,
    adjacency_matrix_model n matrix g inf ->
    Zlength visited = n ->
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    visited_matches_state g s visited ->
    visited_matches_state g s_next (replace_Znth minIndex 1 visited).
Proof.
  intros n matrix g inf s s_next edge_parent minIndex visited
         Hmodel Hlen Hadd Hvisited.
  destruct Hadd as [u [v [Hpair [HaddEdge Hnext_eq]]]].
  assert (Hadd_full :
    selected_parent_add_to_mst g s s_next edge_parent minIndex).
  { exists u, v. split; [exact Hpair | split; [exact HaddEdge | exact Hnext_eq]]. }
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [-> [Hu [Hvout Hstep]]].
  assert (Hmin_graph : In minIndex (graph_vertices g)).
  { change (vvalid g minIndex). eapply step_vvalid2; eauto. }
  unfold visited_matches_state in *.
  intros x Hx_graph.
  rewrite (selected_parent_add_to_mst_vvalid
    g s s_next edge_parent minIndex x Hadd_full).
  destruct (Z.eq_dec x minIndex) as [Hx_eq | Hx_neq].
  - subst x.
    assert (Hrange : 0 <= minIndex < n).
    {
      unfold adjacency_matrix_model in Hmodel.
      destruct Hmodel as [_ [Hvertices _]].
      apply Hvertices in Hmin_graph.
      rewrite <- In_Zrange in Hmin_graph.
      exact Hmin_graph.
    }
    rewrite Znth_replace_Znth_same_local by (rewrite Hlen; exact Hrange).
    split; intros _; [right; reflexivity | lia].
  - assert (Hrange_x : 0 <= x < n).
    {
      unfold adjacency_matrix_model in Hmodel.
      destruct Hmodel as [_ [Hvertices _]].
      apply Hvertices in Hx_graph.
      rewrite <- In_Zrange in Hx_graph.
      exact Hx_graph.
    }
    assert (Hrange_min : 0 <= minIndex < n).
    {
      unfold adjacency_matrix_model in Hmodel.
      destruct Hmodel as [_ [Hvertices _]].
      apply Hvertices in Hmin_graph.
      rewrite <- In_Zrange in Hmin_graph.
      exact Hmin_graph.
    }
    assert (Hrange_min_len : 0 <= minIndex < Zlength visited)
      by (rewrite Hlen; lia).
    assert (Hrange_x_len : 0 <= x < Zlength visited)
      by (rewrite Hlen; lia).
    rewrite (Znth_replace_Znth_diff_local
      visited minIndex x 1 Hrange_min_len Hrange_x_len
      ltac:(intro Heq; apply Hx_neq; symmetry; exact Heq)).
    rewrite Hvisited by exact Hx_graph.
    split; intros H.
    + left; exact H.
    + destruct H as [H | H]; [exact H | contradiction].
Qed.

Lemma selected_parent_add_to_mst_visited_matches_replaced_len :
  forall n matrix g inf s s_next edge_parent minIndex visited,
    adjacency_matrix_model n matrix g inf ->
    Zlength (replace_Znth minIndex 1 visited) = n ->
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    visited_matches_state g s visited ->
    visited_matches_state g s_next (replace_Znth minIndex 1 visited).
Proof.
  intros n matrix g inf s s_next edge_parent minIndex visited
         Hmodel Hreplace_len Hadd Hvisited.
  eapply selected_parent_add_to_mst_visited_matches; eauto.
  rewrite <- Hreplace_len.
  symmetry.
  apply Zlength_replace_Znth_local.
Qed.

Lemma selected_parent_add_to_mst_parent_edges_match :
  forall g src s s_next edge_parent minIndex,
    growing_subgraph_state g s ->
    selected_edges_match_state g src s edge_parent ->
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    selected_edges_match_state g src s_next edge_parent.
Proof.
  intros g src s s_next edge_parent minIndex Hstate Hparent Hadd.
  pose proof Hadd as Hadd_full.
  destruct Hparent as [Hsrc [Hrange Hexact]].
  destruct Hstate as [Hsvalid [_ _]].
  destruct Hadd as [u [v [Hpair [HaddEdge _]]]].
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [-> [Hu [Hvout Hstep]]].
  assert (Hmin_graph : In minIndex (graph_vertices g)).
  { change (vvalid g minIndex). eapply step_vvalid2; eauto. }
  assert (Hmin_not_src : minIndex <> src).
  { intros ->. apply Hvout. exact Hsrc. }
  split.
  - eapply selected_parent_add_to_mst_old_vvalid; eauto.
  - split.
    + intros x Hx_graph Hx_not_src Hx_next.
      rewrite (selected_parent_add_to_mst_vvalid
        g s s_next edge_parent minIndex x Hadd_full) in Hx_next.
      destruct Hx_next as [Hx_old | Hx_new].
      * eapply Hrange; eauto.
      * subst x.
        change (evalid g (Znth minIndex edge_parent default_edge)).
        eapply step_evalid; eauto.
    + intros e.
      rewrite (addEdge_evalid _ _ _ _ _ HaddEdge e).
      split.
      * intros [He_old | He_new].
        -- apply Hexact in He_old.
           destruct He_old as [x [Hx_graph [Hx_not_src [Hx_old Heq]]]].
           exists x.
           repeat split; auto.
           eapply selected_parent_add_to_mst_old_vvalid; eauto.
        -- subst e.
           exists minIndex.
           repeat split; auto.
           ++ eapply selected_parent_add_to_mst_minIndex_vvalid; eauto.
      * intros [x [Hx_graph [Hx_not_src [Hx_next Heq]]]].
        subst e.
        rewrite (selected_parent_add_to_mst_vvalid
          g s s_next edge_parent minIndex x Hadd_full) in Hx_next.
        destruct Hx_next as [Hx_old | Hx_new].
        -- left. apply Hexact.
           exists x. repeat split; auto.
        -- subst x. right. reflexivity.
Qed.

Lemma min_vertex_in_range_empty :
  forall g s inf lowcost edge_parent,
    min_vertex_in_range g s 0 inf (-1) lowcost edge_parent.
Proof.
  intros g s inf lowcost edge_parent.
  unfold min_vertex_in_range.
  left; split; [reflexivity|].
  intros v Hv.
  rewrite <- In_Zrange in Hv.
  lia.
Qed.

Lemma min_vertex_in_range_not_minus_one :
  forall n g s inf minIndex lowcost edge_parent,
    candidate_vertex_exists_in_range n g s lowcost edge_parent inf ->
    min_vertex_in_range g s n inf minIndex lowcost edge_parent ->
    minIndex <> -1.
Proof.
  intros n g s inf minIndex lowcost edge_parent [v [Hv Hcand]] Hmin.
  unfold min_vertex_in_range in Hmin.
  destruct Hmin as [[Hidx Hnone] | [_ [Hin _]]].
  - subst minIndex. specialize (Hnone v Hv). contradiction.
  - intros Hcontra. subst minIndex. rewrite <- In_Zrange in Hin. lia.
Qed.

Lemma cut_edges_covered_by_candidates :
  forall n matrix g s lowcost edge_parent inf,
    adjacency_matrix_model n matrix g inf ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    forall e,
      Prim.is_cut_edge g s e ->
      exists v,
        In v (Zrange 0 n) /\
        candidate_vertex g s lowcost edge_parent inf v /\
        is_cut_edge_to_vertex g s v e.
Proof.
  intros n matrix g s lowcost edge_parent inf Hmodel Hmatch e Hcut.
  destruct Hcut as [u [v [Hu [Hnot_v Hstep]]]].
  exists v.
  assert (Hv_graph : In v (graph_vertices g)).
  {
    pose proof (step_vvalid2 g e u v Hstep) as Hv.
    exact Hv.
  }
  assert (Hv_range : In v (Zrange 0 n)).
  {
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [_ [Hvertices _]].
    rewrite <- Hvertices.
    exact Hv_graph.
  }
  assert (Hendpoint_v : edge_src g e = v \/ edge_dst g e = v).
  {
    unfold step_aux, graph_instance, graph_step in Hstep.
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
  split; [exact Hv_range |].
  split; [| exact Hcut_to_v].
  unfold candidate_vertex.
  split; [exact Hv_graph |].
  split; [exact Hnot_v |].
  destruct Hmatch as [_ Hmatch].
  specialize (Hmatch v Hv_graph Hnot_v).
  destruct Hmatch as [Hparent | [Hnone _]].
  - exact Hparent.
  - exfalso.
    exact (Hnone e Hcut_to_v).
Qed.

Lemma cut_edge_exists_candidate_vertex_exists_in_range :
  forall n matrix g s lowcost edge_parent inf,
    adjacency_matrix_model n matrix g inf ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    (exists e, Prim.is_cut_edge g s e) ->
    candidate_vertex_exists_in_range n g s lowcost edge_parent inf.
Proof.
  intros n matrix g s lowcost edge_parent inf
         Hmodel Hmatch [e Hcut].
  pose proof (cut_edges_covered_by_candidates
    n matrix g s lowcost edge_parent inf Hmodel Hmatch e Hcut)
    as [v [Hv_range [Hcand _]]].
  exists v.
  split; [exact Hv_range | exact Hcand].
Qed.

Lemma unfinished_connected_state_has_candidate_vertex_by_count :
  forall n matrix g s lowcost edge_parent inf,
    adjacency_matrix_model n matrix g inf ->
    connected g ->
    growing_subgraph_state g s ->
    (exists x, vvalid s.(Prim.graph_in_state) x) ->
    state_vertex_count s < n ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    candidate_vertex_exists_in_range n g s lowcost edge_parent inf.
Proof.
  intros n matrix g s lowcost edge_parent inf
         Hmodel Hconn Hgrow Hnonempty Hlt Hmatch.
  eapply cut_edge_exists_candidate_vertex_exists_in_range; eauto.
  eapply has_cut_edge_exists_by_state_vertex_count; eauto.
Qed.

Lemma min_vertex_parent_is_min_cut_edge :
  forall n matrix g s lowcost edge_parent inf minIndex,
    adjacency_matrix_model n matrix g inf ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    min_vertex_in_range g s n inf minIndex lowcost edge_parent ->
    minIndex <> -1 ->
    selected_parent_edge_is_min_cut_edge g s edge_parent minIndex.
Proof.
  intros n matrix g s lowcost edge_parent inf minIndex
         Hmodel Hmatch Hloop HminIndex.
  pose proof (cut_edges_covered_by_candidates
    n matrix g s lowcost edge_parent inf Hmodel Hmatch) as Hcut_cover.
  destruct Hloop as [[HminIndex_eq _] | Hsome].
  - contradiction.
  - destruct Hsome as [Hcand_minIndex [Hrange_minIndex Hmin_vertex]].
    unfold candidate_vertex in Hcand_minIndex.
    destruct Hcand_minIndex as [_ [_ Hparent_minIndex]].
    unfold vertex_has_parent_edge in Hparent_minIndex.
    destruct Hparent_minIndex as
      [_ [_ [Hmin_edge_to_minIndex Hweight_minIndex]]].
    unfold is_min_cut_edge_to_vertex in Hmin_edge_to_minIndex.
    destruct Hmin_edge_to_minIndex as
      [Hcut_to_minIndex Hmin_edge_to_minIndex].
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
      unfold candidate_vertex in Hcand_v.
      destruct Hcand_v as [_ [_ Hparent_v]].
      unfold vertex_has_parent_edge in Hparent_v.
      destruct Hparent_v as [_ [_ [Hmin_edge_to_v Hweight_v]]].
      unfold is_min_cut_edge_to_vertex in Hmin_edge_to_v.
      destruct Hmin_edge_to_v as [_ Hmin_edge_to_v].
      eapply Z_op_le_trans with (y := Some (Znth v lowcost 0)).
      * replace (weight g (Znth minIndex edge_parent default_edge))
          with (Some (Znth minIndex lowcost 0))
          by (symmetry; exact Hweight_minIndex).
        exact (Hmin_vertex v Hrange_v (proj2 Hin_candidate)).
      * replace (Some (Znth v lowcost 0))
          with (weight g (Znth v edge_parent default_edge))
          by exact Hweight_v.
        apply Hmin_edge_to_v.
        exact Hcut_to_v_e.
Qed.

Lemma is_cut_edge_to_vertex_pair :
  forall g s edge_parent minIndex,
    is_cut_edge_to_vertex g s minIndex
      (Znth minIndex edge_parent default_edge) ->
    exists u,
      selected_parent_pair g s edge_parent minIndex u minIndex.
Proof.
  intros g s edge_parent minIndex Hcut_to.
  destruct Hcut_to as [Hout [Hendpoint Hcut]].
  destruct Hcut as [u [v [Hu [Hv Hstep]]]].
  exists u.
  unfold selected_parent_pair.
  split; [reflexivity |].
  split; [exact Hu |].
  split; [exact Hout |].
  unfold step_aux, graph_instance, graph_step in Hstep.
  destruct Hstep as [He [Hends [[Hu_eq Hv_eq] | [Hu_eq Hv_eq]]]]; subst.
  - destruct Hendpoint as [Hsrc | Hdst].
    + exfalso.
      apply Hout.
      rewrite <- Hsrc.
      exact Hu.
    + exact (conj He (conj Hends (or_introl (conj eq_refl (eq_sym Hdst))))).
  - destruct Hendpoint as [Hsrc | Hdst].
    + exact (conj He (conj Hends (or_intror (conj eq_refl (eq_sym Hsrc))))).
    + exfalso.
      apply Hout.
      rewrite <- Hdst.
      exact Hu.
Qed.

Lemma min_vertex_parent_pair_exists :
  forall n g s lowcost edge_parent inf minIndex,
    min_vertex_in_range g s n inf minIndex lowcost edge_parent ->
    minIndex <> -1 ->
    exists u,
      selected_parent_pair g s edge_parent minIndex u minIndex.
Proof.
  intros n g s lowcost edge_parent inf minIndex Hloop HminIndex.
  unfold min_vertex_in_range in Hloop.
  destruct Hloop as [[Hidx _] | [Hcand _]].
  - contradiction.
  - unfold candidate_vertex in Hcand.
    destruct Hcand as [_ [_ Hparent]].
    unfold vertex_has_parent_edge in Hparent.
    destruct Hparent as [_ [_ [Hmin_edge _]]].
    unfold is_min_cut_edge_to_vertex in Hmin_edge.
    destruct Hmin_edge as [Hcut_to _].
    eapply is_cut_edge_to_vertex_pair.
    exact Hcut_to.
Qed.

Lemma candidate_vertex_from_lowcost_lt_inf :
  forall n matrix g s lowcost edge_parent visited inf v,
    adjacency_matrix_model n matrix g inf ->
    visited_matches_state g s visited ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    0 <= v < n ->
    Znth v visited 0 = 0 ->
    Znth v lowcost 0 < inf ->
    candidate_vertex g s lowcost edge_parent inf v.
Proof.
  intros n matrix g s lowcost edge_parent visited inf v
         Hmodel Hvisited Hmatch Hv_range Hvisited0 Hlow_lt.
  assert (Hv_graph : In v (graph_vertices g)).
  {
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [_ [Hvertices _]].
    apply Hvertices.
    rewrite <- In_Zrange.
    lia.
  }
  assert (Hv_not_valid : ~ vvalid s.(Prim.graph_in_state) v).
  {
    intro Hv_valid.
    destruct (Hvisited v Hv_graph) as [_ Hvalid_to_visited].
    pose proof (Hvalid_to_visited Hv_valid) as Hvisited_nonzero.
    lia.
  }
  unfold candidate_vertex.
  split; [exact Hv_graph |].
  split; [exact Hv_not_valid |].
  destruct Hmatch as [_ Hmatch].
  specialize (Hmatch v Hv_graph Hv_not_valid).
  destruct Hmatch as [Hparent | Hnone].
  - exact Hparent.
  - destruct Hnone as [_ Hlow_eq].
    lia.
Qed.

Lemma selected_parent_Prim_body_rel :
  forall g s s_next edge_parent minIndex,
    selected_parent_edge_is_min_cut_edge g s edge_parent minIndex ->
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    @Prim.Prim_body G V E graph_instance g edge_weight_instance s tt s_next.
Proof.
  intros g s s_next edge_parent minIndex Hmin Hadd.
  destruct Hadd as [u [v [Hpair [Hadd _]]]].
  unfold selected_parent_pair in Hpair.
  destruct Hpair as [_ Hpair_core].
  unfold Prim.Prim_body, Prim.get_min_cut_edge, Prim.add_to_mst.
  unfold StateRelMonad.bind, get, update.
  exists (Znth minIndex edge_parent default_edge), s.
  split; [split; [exact Hmin | reflexivity] |].
  exists (u, v), s.
  split; [split; [exact Hpair_core | reflexivity] |].
  exact Hadd.
Qed.

Lemma selected_parent_prim2_loop_step :
  forall n matrix g inf i X s s_next edge_parent minIndex,
    gvalid g ->
    adjacency_matrix_model n matrix g inf ->
    1 <= i ->
    i < n ->
    safeExec (prim_state_is s) (Prim2_loop g (i - 1)) X ->
    selected_parent_edge_is_min_cut_edge g s edge_parent minIndex ->
    selected_parent_add_to_mst g s s_next edge_parent minIndex ->
    safeExec (prim_state_is s_next) (Prim2_loop g i) X.
Proof.
  intros n matrix g inf i X s s_next edge_parent minIndex
         Hg Hmodel Hi_low Hi_high Hsafe Hmin Hadd.
  assert (Hhi : Zlength (bijective_listV g) = n).
  { eapply adjacency_matrix_bijective_vertex_count; eauto. }
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
  forall n matrix g inf i X s,
    gvalid g ->
    adjacency_matrix_model n matrix g inf ->
    i >= n ->
    i <= n ->
    safeExec (prim_state_is s) (Prim2_loop g (i - 1)) X ->
    safeExec (prim_state_is s) (return tt) X.
Proof.
  intros n matrix g inf i X s Hg Hmodel Hi_ge Hi_le Hsafe.
  assert (Hhi : Zlength (bijective_listV g) = n).
  { eapply adjacency_matrix_bijective_vertex_count; eauto. }
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

Lemma min_vertex_in_range_take_current :
  forall g s j inf minIndex lowcost edge_parent,
    0 <= j ->
    candidate_vertex g s lowcost edge_parent inf j ->
    min_vertex_in_range g s j inf minIndex lowcost edge_parent ->
    (minIndex = -1 \/ Znth j lowcost 0 < Znth minIndex lowcost 0) ->
    min_vertex_in_range g s (j + 1) inf j lowcost edge_parent.
Proof.
  intros g s j inf minIndex lowcost edge_parent Hj Hcand_j Hmin Hbetter.
  unfold min_vertex_in_range in *.
  right.
  split; [exact Hcand_j|].
  split.
  - rewrite <- In_Zrange. lia.
  - intros v Hv Hcand_v.
    rewrite <- In_Zrange in Hv.
    destruct (Z.eq_dec v j) as [-> | Hneq].
    + lia.
    + assert (Hv_old : In v (Zrange 0 j)) by (rewrite <- In_Zrange; lia).
      destruct Hmin as [[Hidx Hnone] | [_ [Hmin_in Hle]]].
      * specialize (Hnone v Hv_old). contradiction.
      * destruct Hbetter as [Hidx | Hlt].
        -- subst minIndex.
           rewrite <- In_Zrange in Hmin_in.
           lia.
        -- specialize (Hle v Hv_old Hcand_v). lia.
Qed.

Lemma min_vertex_in_range_take_current_from_arrays :
  forall n matrix g s j inf min minIndex lowcost edge_parent visited,
    adjacency_matrix_model n matrix g inf ->
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
  intros n matrix g s j inf min minIndex lowcost edge_parent visited
         Hmodel Hvisited Hmatch Hmin Hj_range Hvisited0 Hlow_lt
         Hmin_none Hmin_some.
  assert (Hlow_inf : Znth j lowcost 0 < inf).
  {
    destruct (Z.eq_dec minIndex (-1)) as [Hidx | Hidx].
    - rewrite Hmin_none in Hlow_lt by exact Hidx.
      exact Hlow_lt.
    - rewrite Hmin_some in Hlow_lt by exact Hidx.
      unfold min_vertex_in_range in Hmin.
      destruct Hmin as [[Hminus _] | [Hcand_min _]]; [contradiction|].
      unfold candidate_vertex in Hcand_min.
      destruct Hcand_min as [_ [_ Hparent]].
      unfold vertex_has_parent_edge in Hparent.
      destruct Hparent as [_ [Hlow_min _]].
      lia.
  }
  eapply min_vertex_in_range_take_current.
  - lia.
  - eapply candidate_vertex_from_lowcost_lt_inf; eauto.
  - exact Hmin.
  - destruct (Z.eq_dec minIndex (-1)) as [Hidx | Hidx].
    + left; exact Hidx.
    + right.
      rewrite Hmin_some in Hlow_lt by exact Hidx.
      exact Hlow_lt.
Qed.

Lemma min_vertex_in_range_skip_not_candidate :
  forall g s j inf minIndex lowcost edge_parent,
    0 <= j ->
    ~ candidate_vertex g s lowcost edge_parent inf j ->
    min_vertex_in_range g s j inf minIndex lowcost edge_parent ->
    min_vertex_in_range g s (j + 1) inf minIndex lowcost edge_parent.
Proof.
  intros g s j inf minIndex lowcost edge_parent Hj Hnot Hmin.
  unfold min_vertex_in_range in *.
  destruct Hmin as [[Hidx Hnone] | [Hcand_min [Hmin_in Hle]]].
  - left. split; [exact Hidx|].
    intros v Hv. rewrite <- In_Zrange in Hv.
    destruct (Z.eq_dec v j) as [-> | Hneq]; [exact Hnot|].
    apply Hnone. rewrite <- In_Zrange. lia.
  - right. split; [exact Hcand_min|].
    split.
    + rewrite <- In_Zrange in Hmin_in. rewrite <- In_Zrange. lia.
    + intros v Hv Hcand_v. rewrite <- In_Zrange in Hv.
      destruct (Z.eq_dec v j) as [-> | Hneq]; [contradiction|].
      apply Hle; [rewrite <- In_Zrange; lia | exact Hcand_v].
Qed.

Lemma min_vertex_in_range_skip_not_better :
  forall g s j inf minIndex lowcost edge_parent,
    0 <= j ->
    candidate_vertex g s lowcost edge_parent inf j ->
    min_vertex_in_range g s j inf minIndex lowcost edge_parent ->
    minIndex <> -1 ->
    Znth minIndex lowcost 0 <= Znth j lowcost 0 ->
    min_vertex_in_range g s (j + 1) inf minIndex lowcost edge_parent.
Proof.
  intros g s j inf minIndex lowcost edge_parent Hj Hcand_j Hmin Hidx_not_minus Hnot_better.
  unfold min_vertex_in_range in *.
  destruct Hmin as [[Hidx Hnone] | [Hcand_min [Hmin_in Hle]]].
  - contradiction.
  - right. split; [exact Hcand_min|].
    split.
    + rewrite <- In_Zrange in Hmin_in. rewrite <- In_Zrange. lia.
    + intros v Hv Hcand_v. rewrite <- In_Zrange in Hv.
      destruct (Z.eq_dec v j) as [-> | Hneq].
      * exact Hnot_better.
      * apply Hle; [rewrite <- In_Zrange; lia | exact Hcand_v].
Qed.

Lemma min_vertex_in_range_skip_not_better_from_value :
  forall g s j inf min minIndex lowcost edge_parent,
    0 <= j ->
    min_vertex_in_range g s j inf minIndex lowcost edge_parent ->
    Znth j lowcost 0 >= min ->
    (minIndex = -1 -> min = inf) ->
    (minIndex <> -1 -> min = Znth minIndex lowcost 0) ->
    min_vertex_in_range g s (j + 1) inf minIndex lowcost edge_parent.
Proof.
  intros g s j inf min minIndex lowcost edge_parent
         Hj Hmin_range Hlow_ge Hmin_none Hmin_some.
  unfold min_vertex_in_range in *.
  destruct Hmin_range as [[Hidx_none Hnone] | [Hcand_idx [Hidx_in Hle]]].
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
      unfold candidate_vertex in Hcand_j.
      destruct Hcand_j as [_ [_ Hparent]].
      unfold vertex_has_parent_edge in Hparent.
      destruct Hparent as [_ [Hlow_j _]].
      rewrite (Hmin_none Hidx_none) in Hlow_ge.
      lia.
  - right.
    split; [exact Hcand_idx |].
    split.
    + rewrite Zrange_0_snoc by lia.
      apply in_or_app; left; exact Hidx_in.
    + intros v Hv_in Hcand_v.
      rewrite Zrange_0_snoc in Hv_in by lia.
      apply in_app_or in Hv_in.
      destruct Hv_in as [Hv_old | Hv_last].
      * apply Hle; [exact Hv_old | exact Hcand_v].
      * simpl in Hv_last.
        destruct Hv_last as [Hv_eq | []].
        subst v.
        assert (Hidx_not_minus_one : minIndex <> -1).
        {
          rewrite <- In_Zrange in Hidx_in.
          lia.
        }
        rewrite (Hmin_some Hidx_not_minus_one) in Hlow_ge.
        lia.
Qed.

(** ** 扫描矩阵一行时对 [lowcost] 和 ghost [edge_parent] 的更新 *)

Definition scan_one_matrix_neighbor_update
    (g : G) (matrix : list (list Z)) (inf : Z)
    (s : St) (from_v v : V)
    (lowcost_in : list Z) (edge_parent_in : list E)
    (lowcost_out : list Z) (edge_parent_out : list E) : Prop :=
  ((~ vvalid s.(Prim.graph_in_state) v /\
    matrix_entry matrix from_v v <> inf /\
    matrix_entry matrix from_v v < Znth v lowcost_in 0 /\
    graph_step g (undirected_edge from_v v) from_v v /\
    weight g (undirected_edge from_v v) = Some (matrix_entry matrix from_v v) /\
    lowcost_out = replace_Znth v (matrix_entry matrix from_v v) lowcost_in /\
    edge_parent_out = replace_Znth v (undirected_edge from_v v) edge_parent_in) \/
   ((vvalid s.(Prim.graph_in_state) v \/
     matrix_entry matrix from_v v = inf \/
     Znth v lowcost_in 0 <= matrix_entry matrix from_v v) /\
	    lowcost_out = lowcost_in /\
	    edge_parent_out = edge_parent_in)).

Definition matrix_row_edge_for_vertex
    (g : G) (s : St) (from_v v : V) (e : E) : Prop :=
  is_cut_edge_to_vertex g s v e /\
  (edge_src g e = from_v \/ edge_dst g e = from_v).

Definition add_matrix_row_edge_for_vertex
    (g : G) (s : St) (from_v cur : V)
    (edge_for_vertex : V -> E -> Prop)
    (v : V) (e : E) : Prop :=
  edge_for_vertex v e \/
  (v = cur /\ matrix_row_edge_for_vertex g s from_v v e).

Fixpoint add_matrix_row_edges_for_vertex
    (g : G) (s : St) (from_v : V) (scanned : list V)
    (edge_for_vertex : V -> E -> Prop) : V -> E -> Prop :=
  match scanned with
  | nil => edge_for_vertex
  | cur :: rest =>
      add_matrix_row_edges_for_vertex g s from_v rest
        (add_matrix_row_edge_for_vertex g s from_v cur edge_for_vertex)
  end.

Lemma add_matrix_row_edges_for_vertex_iff :
  forall g s from_v scanned edge_for_vertex v e,
    add_matrix_row_edges_for_vertex g s from_v scanned edge_for_vertex v e <->
      edge_for_vertex v e \/
      (In v scanned /\ matrix_row_edge_for_vertex g s from_v v e).
Proof.
  intros g s from_v scanned.
  induction scanned as [| cur rest IH];
    intros edge_for_vertex v e; simpl.
  - split.
    + intros H; left; exact H.
    + intros [H | [Hnil _]]; [exact H | contradiction].
  - rewrite IH.
    unfold add_matrix_row_edge_for_vertex.
    split.
    + intros [[Hold | [Hvcur Hrow]] | [Hrest Hrow]].
      * left; exact Hold.
      * right. split; [simpl; left; symmetry; exact Hvcur | exact Hrow].
      * right. split; [simpl; right; exact Hrest | exact Hrow].
    + intros [Hold | [[Hvcur | Hrest] Hrow]].
      * left; left; exact Hold.
      * left; right. split; [symmetry; exact Hvcur | exact Hrow].
      * right. split; [exact Hrest | exact Hrow].
Qed.

Lemma is_cut_edge_to_vertex_after_add_row_iff :
  forall n matrix g inf s s_after edge_parent minIndex v e,
    adjacency_matrix_model n matrix g inf ->
    selected_parent_add_to_mst g s s_after edge_parent minIndex ->
    In v (graph_vertices g) ->
    ~ vvalid s_after.(Prim.graph_in_state) v ->
    (is_cut_edge_to_vertex g s v e \/
     (In v (Zrange 0 n) /\
      matrix_row_edge_for_vertex g s_after minIndex v e)) <->
    is_cut_edge_to_vertex g s_after v e.
Proof.
  intros n matrix g inf s s_after edge_parent minIndex v e
         Hmodel Hadd Hv_graph Hvout_after.
  split.
  - intros [Hold | [_ Hrow]].
    + unfold is_cut_edge_to_vertex in *.
      destruct Hold as [Hvout_old [Hendpoint Hcut_old]].
      split; [exact Hvout_after |].
      split; [exact Hendpoint |].
      destruct Hcut_old as [u [w [Hu_old [Hwout_old Hstep]]]].
      exists u, w.
      split.
      { eapply selected_parent_add_to_mst_old_vvalid; eauto. }
      split; [| exact Hstep].
      assert (Hw_eq_v : w = v).
      {
        unfold step_aux, graph_instance, graph_step in Hstep.
        destruct e as [a b]; simpl in *.
        destruct Hstep as [_ [_ Hendpoints]].
        destruct Hendpoints as [[Ha Hb] | [Ha Hb]]; subst;
          destruct Hendpoint as [Hendpoint | Hendpoint]; simpl in *; subst; auto;
          exfalso; apply Hvout_after;
          eapply selected_parent_add_to_mst_old_vvalid; eauto.
      }
      subst w.
      exact Hvout_after.
    + unfold matrix_row_edge_for_vertex in Hrow.
      exact (proj1 Hrow).
  - intros Hafter.
    unfold is_cut_edge_to_vertex in Hafter.
    destruct Hafter as [Hvout_after' [Hendpoint Hcut_after]].
    destruct Hcut_after as [u [w [Hu_after [Hwout_after Hstep]]]].
    rewrite (selected_parent_add_to_mst_vvalid
      g s s_after edge_parent minIndex u Hadd) in Hu_after.
    destruct Hu_after as [Hu_old | Hu_min].
    + left.
      unfold is_cut_edge_to_vertex.
      split.
      { intros Hv_old.
        apply Hvout_after.
        eapply selected_parent_add_to_mst_old_vvalid; eauto. }
      split; [exact Hendpoint |].
      exists u, w.
      split; [exact Hu_old |].
      split; [| exact Hstep].
      intros Hw_old.
      apply Hwout_after.
      eapply selected_parent_add_to_mst_old_vvalid; eauto.
    + right.
      split.
      {
        unfold adjacency_matrix_model in Hmodel.
        destruct Hmodel as [_ [Hvertices _]].
        rewrite <- Hvertices.
        exact Hv_graph.
      }
      unfold matrix_row_edge_for_vertex.
      split.
	      {
	        unfold is_cut_edge_to_vertex.
	        split; [exact Hvout_after |].
	        split; [exact Hendpoint |].
	        exists u, w.
	        split.
	        { rewrite (selected_parent_add_to_mst_vvalid
	            g s s_after edge_parent minIndex u Hadd).
	          right; exact Hu_min. }
	        split; [exact Hwout_after | exact Hstep].
	      }
      subst u.
      unfold step_aux, graph_instance, graph_step in Hstep.
      destruct e as [a b]; simpl in *.
      destruct Hstep as [_ [_ Hendpoints]].
      destruct Hendpoints as [[Ha Hb] | [Ha Hb]]; subst; simpl; auto.
Qed.

Lemma matrix_row_edge_weight :
  forall n matrix g inf s from_v v e,
    adjacency_matrix_model n matrix g inf ->
    vvalid s.(Prim.graph_in_state) from_v ->
    matrix_row_edge_for_vertex g s from_v v e ->
    weight g e = Some (matrix_entry matrix from_v v).
Proof.
  intros n matrix g inf s from_v v e Hmodel Hfrom Hrow.
  unfold matrix_row_edge_for_vertex in Hrow.
  destruct Hrow as [Hcut_to Htouch].
  unfold is_cut_edge_to_vertex in Hcut_to.
  destruct Hcut_to as [Hvout [Hendpoint Hcut]].
  destruct Hcut as [u [w [Hu [Hwout Hstep]]]].
  unfold step_aux, graph_instance, graph_step in Hstep.
  destruct Hstep as [Hin [Hends Hendpoints]].
  unfold edge_src, edge_dst in *.
  destruct e as [a b]; simpl in *.
  assert (Heq : (a = from_v /\ b = v) \/ (a = v /\ b = from_v)).
  {
    destruct Htouch as [Ha | Hb];
    destruct Hendpoint as [Hvsrc | Hvdst]; subst; simpl in *; auto.
    - exfalso. apply Hvout. exact Hfrom.
    - exfalso. apply Hvout. exact Hfrom.
  }
  unfold adjacency_matrix_model in Hmodel.
  destruct Hmodel as [_ [_ [_ [_ [Hedge _]]]]].
  specialize (Hedge (a, b) Hin).
  destruct Hedge as [_ [Hwt_forward [Hwt_backward _]]].
  unfold weight, edge_weight_instance; simpl.
  destruct Heq as [[-> ->] | [-> ->]].
  - f_equal. exact Hwt_forward.
  - f_equal. exact Hwt_backward.
Qed.

Lemma matrix_row_edge_entry_not_minus_one :
  forall n matrix g inf s from_v v e,
    adjacency_matrix_model n matrix g inf ->
    vvalid s.(Prim.graph_in_state) from_v ->
    matrix_row_edge_for_vertex g s from_v v e ->
    matrix_entry matrix from_v v <> inf.
Proof.
  intros n matrix g inf s from_v v e Hmodel Hfrom Hrow.
  pose proof (matrix_row_edge_weight
    n matrix g inf s from_v v e Hmodel Hfrom Hrow) as Hweight_row.
  unfold matrix_row_edge_for_vertex in Hrow.
  destruct Hrow as [Hcut_to _].
  unfold is_cut_edge_to_vertex in Hcut_to.
  destruct Hcut_to as [_ [_ Hcut]].
  destruct Hcut as [u [w [_ [_ Hstep]]]].
  unfold step_aux, graph_instance, graph_step in Hstep.
  destruct Hstep as [Hin [_ _]].
  unfold adjacency_matrix_model in Hmodel.
  destruct Hmodel as [_ [_ [_ [_ [Hedge _]]]]].
  specialize (Hedge e Hin).
  destruct Hedge as [_ [_ [_ Hnot_minus]]].
  unfold weight, edge_weight_instance in Hweight_row.
  simpl in Hweight_row.
  inversion Hweight_row as [Hgraph_weight_eq].
  exact Hnot_minus.
Qed.

Lemma scan_one_matrix_neighbor_update_take :
  forall n g matrix inf s from_v v lowcost edge_parent,
    adjacency_matrix_model n matrix g inf ->
    0 <= from_v < n ->
    0 <= v < n ->
    ~ vvalid s.(Prim.graph_in_state) v ->
    matrix_entry matrix from_v v <> inf ->
    matrix_entry matrix from_v v < Znth v lowcost 0 ->
    scan_one_matrix_neighbor_update g matrix inf s from_v v
      lowcost edge_parent
      (replace_Znth v (matrix_entry matrix from_v v) lowcost)
      (replace_Znth v (undirected_edge from_v v) edge_parent).
Proof.
  intros n g matrix inf s from_v v lowcost edge_parent
         Hmodel Hfrom Hv Hnot Hedge Hlt.
  left.
  pose proof (adjacency_matrix_model_edge n matrix g inf from_v v Hmodel Hfrom Hv Hedge)
    as [_ [Hstep Hweight]].
  split; [exact Hnot|].
  split; [exact Hedge|].
  split; [exact Hlt|].
  split; [exact Hstep|].
  split; [exact Hweight|].
  split; reflexivity.
Qed.

Lemma scan_one_matrix_neighbor_update_skip :
  forall g matrix inf s from_v v lowcost edge_parent,
    (vvalid s.(Prim.graph_in_state) v \/
     matrix_entry matrix from_v v = inf \/
     Znth v lowcost 0 <= matrix_entry matrix from_v v) ->
    scan_one_matrix_neighbor_update g matrix inf s from_v v
      lowcost edge_parent lowcost edge_parent.
Proof.
  intros g matrix inf s from_v v lowcost edge_parent Hskip.
  right.
  repeat split; auto.
Qed.

Lemma scan_one_matrix_neighbor_update_lengths :
  forall g matrix inf s from_v v
         lowcost_in edge_parent_in lowcost_out edge_parent_out,
    scan_one_matrix_neighbor_update g matrix inf s from_v v
      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
    Zlength lowcost_out = Zlength lowcost_in /\
    Zlength edge_parent_out = Zlength edge_parent_in.
Proof.
  intros g matrix inf s from_v v lowcost_in edge_parent_in
         lowcost_out edge_parent_out Hscan.
  unfold scan_one_matrix_neighbor_update in Hscan.
  destruct Hscan as
    [[_ [_ [_ [_ [_ [Hlow Hparent]]]]]]
    | [_ [Hlow Hparent]]];
    subst; split; try apply Zlength_replace_Znth_local; reflexivity.
Qed.

Lemma scan_one_matrix_neighbor_update_lowcost_bound :
  forall n g matrix inf s from_v cur
         lowcost_in edge_parent_in lowcost_out edge_parent_out,
    adjacency_matrix_model n matrix g inf ->
    0 <= inf ->
    0 <= from_v < n ->
    0 <= cur < n ->
    Zlength lowcost_in = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k lowcost_in 0 <= inf) ->
    scan_one_matrix_neighbor_update g matrix inf s from_v cur
      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
    forall k, 0 <= k < n -> 0 <= Znth k lowcost_out 0 <= inf.
Proof.
  intros n g matrix inf s from_v cur lowcost_in edge_parent_in
         lowcost_out edge_parent_out Hmodel Hinf Hfrom Hcur Hlen Hbound Hscan k Hk.
  unfold scan_one_matrix_neighbor_update in Hscan.
  destruct Hscan as
    [[_ [Hedge [_ [_ [_ [Hlow _]]]]]]
    | [_ [Hlow _]]].
  - subst lowcost_out.
    destruct (Z.eq_dec k cur) as [-> | Hneq].
    + rewrite Znth_replace_Znth_same_local by lia.
      unfold adjacency_matrix_model in Hmodel.
      destruct Hmodel as [_ [_ [Hentry _]]].
      specialize (Hentry from_v cur Hfrom Hcur).
      destruct Hentry as [Heq | Hrange]; [contradiction|lia].
    + rewrite Znth_replace_Znth_diff_local by lia.
      apply Hbound; exact Hk.
  - subst lowcost_out.
    apply Hbound; exact Hk.
Qed.

Lemma scan_one_matrix_neighbor_update_target :
  forall g matrix inf s from_v v
         lowcost_in edge_parent_in lowcost_out edge_parent_out,
    scan_one_matrix_neighbor_update g matrix inf s from_v v
      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
    vvalid s.(Prim.graph_in_state) from_v ->
    0 <= v < Zlength lowcost_in ->
    0 <= v < Zlength edge_parent_in ->
    ((is_cut_edge_to_vertex g s v (undirected_edge from_v v) /\
      matrix_entry matrix from_v v < Znth v lowcost_in 0 /\
      weight g (undirected_edge from_v v) = Some (matrix_entry matrix from_v v) /\
      Znth v lowcost_out 0 = matrix_entry matrix from_v v /\
      Znth v edge_parent_out default_edge = undirected_edge from_v v) \/
     ((vvalid s.(Prim.graph_in_state) v \/
       matrix_entry matrix from_v v = inf \/
       Znth v lowcost_in 0 <= matrix_entry matrix from_v v) /\
      Znth v lowcost_out 0 = Znth v lowcost_in 0 /\
      Znth v edge_parent_out default_edge = Znth v edge_parent_in default_edge)).
Proof.
  intros g matrix inf s from_v v lowcost_in edge_parent_in
         lowcost_out edge_parent_out Hscan Hfrom_valid Hlow_range Hparent_range.
  unfold scan_one_matrix_neighbor_update in Hscan.
  destruct Hscan as
    [[Hvout [Hedge [Hlt [Hstep [Hweight [Hlow Hparent]]]]]]
    | [Hskip [Hlow Hparent]]].
  - subst lowcost_out edge_parent_out.
    left.
    split.
    + unfold is_cut_edge_to_vertex.
      split; [exact Hvout|].
      split.
      {
        unfold edge_src, edge_dst, undirected_edge; simpl.
        destruct (Z.leb_spec0 from_v v); simpl; auto.
      }
      exists from_v, v.
      split.
      * exact Hfrom_valid.
      * split; [exact Hvout| exact Hstep].
    + split; [exact Hlt|].
      split.
      * exact Hweight.
      * split.
        -- apply Znth_replace_Znth_same_local; exact Hlow_range.
        -- apply Znth_replace_Znth_same_any; exact Hparent_range.
  - subst lowcost_out edge_parent_out.
    right.
    split.
    + exact Hskip.
    + split; reflexivity.
Qed.

Lemma scan_one_matrix_neighbor_update_other_vertex :
  forall g matrix inf s from_v cur
         lowcost_in edge_parent_in lowcost_out edge_parent_out v,
    scan_one_matrix_neighbor_update g matrix inf s from_v cur
      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
    0 <= cur < Zlength lowcost_in ->
    0 <= cur < Zlength edge_parent_in ->
    0 <= v < Zlength lowcost_in ->
    0 <= v < Zlength edge_parent_in ->
    v <> cur ->
    Znth v lowcost_out 0 = Znth v lowcost_in 0 /\
    Znth v edge_parent_out default_edge = Znth v edge_parent_in default_edge.
Proof.
  intros g matrix inf s from_v cur lowcost_in edge_parent_in
         lowcost_out edge_parent_out v Hscan Hcur_low Hcur_parent Hv_low Hv_parent Hneq.
  unfold scan_one_matrix_neighbor_update in Hscan.
  destruct Hscan as
    [[_ [_ [_ [_ [_ [Hlow Hparent]]]]]]
    | [_ [Hlow Hparent]]].
  - subst lowcost_out edge_parent_out.
    split.
    + rewrite (Znth_replace_Znth_diff_local lowcost_in cur v
        (matrix_entry matrix from_v cur)); auto; lia.
    + exact (@Znth_replace_Znth_diff_any E edge_parent_in cur v
        (undirected_edge from_v cur) default_edge Hcur_parent Hv_parent ltac:(lia)).
	  - subst lowcost_out edge_parent_out.
	    split; reflexivity.
Qed.

Lemma scan_one_matrix_neighbor_update_selected_edges_match_state :
  forall g matrix inf src s from_v cur
         lowcost_in edge_parent_in lowcost_out edge_parent_out,
    selected_edges_match_state g src s edge_parent_in ->
    (forall v,
       In v (graph_vertices g) ->
       0 <= v < Zlength lowcost_in /\
       0 <= v < Zlength edge_parent_in) ->
    In cur (graph_vertices g) ->
    scan_one_matrix_neighbor_update g matrix inf s from_v cur
      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
    selected_edges_match_state g src s edge_parent_out.
Proof.
  intros g matrix inf src s from_v cur lowcost_in edge_parent_in
         lowcost_out edge_parent_out Hparent Hrange Hcur_graph Hscan.
  assert (Hparent_same :
    forall v,
      In v (graph_vertices g) ->
      vvalid s.(Prim.graph_in_state) v ->
      Znth v edge_parent_out default_edge =
      Znth v edge_parent_in default_edge).
  {
    intros v Hv_graph Hv_valid.
    unfold scan_one_matrix_neighbor_update in Hscan.
    destruct Hscan as
      [[Hcur_out [_ [_ [_ [_ [_ Hparent_out]]]]]]
      | [_ [_ Hparent_out]]].
    - subst edge_parent_out.
      destruct (Z.eq_dec v cur) as [Heq | Hneq].
      + subst cur. contradiction.
      + apply Znth_replace_Znth_diff_any.
        * apply Hrange; exact Hcur_graph.
        * apply Hrange; exact Hv_graph.
        * congruence.
    - subst edge_parent_out. reflexivity.
  }
  destruct Hparent as [Hsrc_valid [Hrange_state Hexact_state]].
  split; [exact Hsrc_valid |].
  split.
  - intros v Hv_graph Hv_src Hv_valid.
    rewrite Hparent_same by auto.
    apply Hrange_state; auto.
  - intros e.
    split; intros H.
    + destruct (proj1 (Hexact_state e) H) as
        [v [Hv_graph [Hv_src [Hv_valid Heq]]]].
      exists v; repeat split; auto.
      rewrite Hparent_same by auto.
      exact Heq.
    + destruct H as [v [Hv_graph [Hv_src [Hv_valid Heq]]]].
      apply (proj2 (Hexact_state e)).
      exists v; repeat split; auto.
      rewrite Hparent_same in Heq by auto.
      exact Heq.
Qed.

Lemma scan_one_matrix_neighbor_update_lowcost_parent_match_by :
  forall n g matrix inf s from_v cur
         eligible_vertex edge_for_vertex
         lowcost_in edge_parent_in lowcost_out edge_parent_out,
    adjacency_matrix_model n matrix g inf ->
    vvalid s.(Prim.graph_in_state) from_v ->
    In cur (graph_vertices g) ->
    matrix_entry matrix from_v cur = inf \/
    matrix_entry matrix from_v cur < inf ->
    (forall v, eligible_vertex v -> ~ vvalid s.(Prim.graph_in_state) v) ->
    lowcost_parent_match_by
      g eligible_vertex edge_for_vertex
      lowcost_in edge_parent_in inf ->
    scan_one_matrix_neighbor_update g matrix inf s from_v cur
      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_in) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_in) ->
    lowcost_parent_match_by
      g eligible_vertex
      (add_matrix_row_edge_for_vertex g s from_v cur edge_for_vertex)
      lowcost_out edge_parent_out inf.
Proof.
  intros n g matrix inf s from_v cur eligible_vertex edge_for_vertex
		         lowcost_in edge_parent_in lowcost_out edge_parent_out
		         Hmodel Hfrom_valid Hcur_graph Hentry_case Helig_out
		         Hmatch Hscan Hlow_range Hparent_range.
  unfold lowcost_parent_match_by in *.
  destruct Hmatch as [Harray_range Hmatch].
  destruct (scan_one_matrix_neighbor_update_lengths
    g matrix inf s from_v cur
    lowcost_in edge_parent_in lowcost_out edge_parent_out Hscan)
    as [Hlow_len Hparent_len].
  split.
  { intros v Hv_graph.
    destruct (Harray_range v Hv_graph) as [Hv_low Hv_parent].
    split; [rewrite Hlow_len; exact Hv_low | rewrite Hparent_len; exact Hv_parent]. }
  intros v Hv_graph Helig.
  assert (Hcur_low : 0 <= cur < Zlength lowcost_in)
    by (apply Hlow_range; exact Hcur_graph).
  assert (Hcur_parent : 0 <= cur < Zlength edge_parent_in)
    by (apply Hparent_range; exact Hcur_graph).
  destruct (Z.eq_dec v cur) as [Hv_eq | Hv_neq].
  - subst v.
    specialize (Hmatch cur Hcur_graph Helig).
    destruct (scan_one_matrix_neighbor_update_target
      g matrix inf s from_v cur
      lowcost_in edge_parent_in lowcost_out edge_parent_out
      Hscan Hfrom_valid Hcur_low Hcur_parent)
	      as [[Hcut_new [Hlt_new [Hweight_new [Hlow_out Hparent_out]]]] |
	          [Hskip [Hlow_out Hparent_out]]].
		    + left.
		      assert (Hentry_lt_inf : matrix_entry matrix from_v cur < inf).
	      {
	        pose proof Hmatch as Hmatch_for_bound.
	        destruct Hmatch_for_bound as [Hold_parent | [_ Hlow_old]].
	        - unfold vertex_has_parent_edge_by in Hold_parent.
	          destruct Hold_parent as [_ [Hold_low _]].
	          lia.
	        - rewrite Hlow_old in Hlt_new.
	          lia.
	      }
	      unfold vertex_has_parent_edge_by.
	      split.
      * unfold is_cut_edge_to_vertex in Hcut_new.
        destruct Hcut_new as [_ [_ [u [w [_ [_ Hstep]]]]]].
        unfold step_aux, graph_instance, graph_step in Hstep.
        rewrite Hparent_out.
        exact (proj1 Hstep).
      * split.
	        -- rewrite Hlow_out. exact Hentry_lt_inf.
        -- split.
	           ++ unfold min_object_of_subset.
	              split.
	              ** right.
	                 rewrite Hparent_out.
	                 split; [reflexivity |].
	                 unfold matrix_row_edge_for_vertex.
	                 split; [exact Hcut_new |].
                 unfold edge_src, undirected_edge; simpl.
                 destruct (Z.leb_spec0 from_v cur); simpl; auto.
              ** intros e' Hedge'.
                 unfold add_matrix_row_edge_for_vertex in Hedge'.
                 destruct Hedge' as [Hold_edge | [_ Hrow_edge]].
	                 --- destruct Hmatch as [Hold_parent | [Hnone_old Hlow_old]].
	                     { unfold vertex_has_parent_edge_by in Hold_parent.
	                       destruct Hold_parent as
	                         [Hold_in [Hold_low [Hold_min Hold_weight]]].
	                       unfold min_object_of_subset in Hold_min.
	                       destruct Hold_min as [_ Hold_le].
                       eapply Z_op_le_trans
                         with (y := Some (Znth cur lowcost_in 0)).
		                       ** rewrite Hparent_out.
		                          rewrite Hweight_new.
		                          unfold Z_op_le; simpl.
		                          apply Z.lt_le_incl; exact Hlt_new.
	                       ** replace (Some (Znth cur lowcost_in 0))
	                            with (weight g (Znth cur edge_parent_in default_edge))
	                            by exact Hold_weight.
	                          apply Hold_le; exact Hold_edge. }
	                     { exfalso. exact (Hnone_old e' Hold_edge). }
	                 --- rewrite (matrix_row_edge_weight n matrix g inf s from_v cur e'
	                       Hmodel Hfrom_valid Hrow_edge).
		                     rewrite Hparent_out.
	                     rewrite Hweight_new.
	                     apply Z_op_le_refl.
	           ++ rewrite Hlow_out.
	              rewrite Hparent_out.
	              exact Hweight_new.
    + destruct Hmatch as [Hold_parent | [Hnone_old Hlow_old]].
      * left.
        unfold vertex_has_parent_edge_by in *.
        destruct Hold_parent as [Hold_in [Hold_low [Hold_min Hold_weight]]].
        split; [rewrite Hparent_out; exact Hold_in |].
        split; [rewrite Hlow_out; exact Hold_low |].
        split.
        -- unfold min_object_of_subset in *.
	           destruct Hold_min as [Hold_subset Hold_le].
	           split.
	           ++ rewrite Hparent_out.
	              left; exact Hold_subset.
           ++ intros e' Hedge'.
	              unfold add_matrix_row_edge_for_vertex in Hedge'.
	              destruct Hedge' as [Hold_edge | [_ Hrow_edge]].
	              ** rewrite Hparent_out.
	                 apply Hold_le; exact Hold_edge.
              ** destruct Hskip as [Hv_in | [Hno_edge | Hnot_better]].
                 --- exfalso.
                     exact (Helig_out cur Helig Hv_in).
                 --- exfalso.
                   exact (matrix_row_edge_entry_not_minus_one
                       n matrix g inf s from_v cur e' Hmodel Hfrom_valid Hrow_edge Hno_edge).
	                 --- rewrite (matrix_row_edge_weight n matrix g inf s from_v cur e'
	                       Hmodel Hfrom_valid Hrow_edge).
	                     rewrite Hparent_out.
		                     replace (weight g (Znth cur edge_parent_in default_edge))
	                       with (Some (Znth cur lowcost_in 0))
	                       by (symmetry; exact Hold_weight).
                     simpl; exact Hnot_better.
	        -- rewrite Hparent_out.
	           rewrite Hlow_out; exact Hold_weight.
      * destruct Hskip as [Hv_in | [Hno_edge | Hnot_better]].
        -- exfalso. exact (Helig_out cur Helig Hv_in).
        -- right.
           split.
           ++ intros e' Hedge'.
              unfold add_matrix_row_edge_for_vertex in Hedge'.
              destruct Hedge' as [Hold_edge | [_ Hrow_edge]].
              ** exact (Hnone_old e' Hold_edge).
              ** exact (matrix_row_edge_entry_not_minus_one
                   n matrix g inf s from_v cur e' Hmodel Hfrom_valid Hrow_edge Hno_edge).
           ++ rewrite Hlow_out; exact Hlow_old.
        -- right.
           split.
           ++ intros e' Hedge'.
              unfold add_matrix_row_edge_for_vertex in Hedge'.
		              destruct Hedge' as [Hold_edge | [_ Hrow_edge]].
		              ** exact (Hnone_old e' Hold_edge).
		              ** destruct Hentry_case as [Hentry_eq_inf | Hentry_lt_inf].
		                 --- exfalso.
		                     assert (Hentry_eq_no_edge :
		                       matrix_entry matrix from_v cur = inf).
		                     { exact Hentry_eq_inf. }
		                     exact (matrix_row_edge_entry_not_minus_one
		                       n matrix g inf s from_v cur e' Hmodel Hfrom_valid Hrow_edge
		                       Hentry_eq_no_edge).
		                 --- rewrite Hlow_old in Hnot_better.
		                     lia.
           ++ rewrite Hlow_out; exact Hlow_old.
  - specialize (Hmatch v Hv_graph Helig).
    assert (Hv_low : 0 <= v < Zlength lowcost_in)
      by (apply Hlow_range; exact Hv_graph).
    assert (Hv_parent : 0 <= v < Zlength edge_parent_in)
      by (apply Hparent_range; exact Hv_graph).
    destruct (scan_one_matrix_neighbor_update_other_vertex
      g matrix inf s from_v cur
      lowcost_in edge_parent_in lowcost_out edge_parent_out v
      Hscan Hcur_low Hcur_parent Hv_low Hv_parent Hv_neq)
      as [Hlow_out_v Hparent_out_v].
    destruct Hmatch as [Hold_parent | [Hnone_old Hlow_old]].
    + left.
      unfold vertex_has_parent_edge_by in *.
      destruct Hold_parent as [Hold_in [Hold_low [Hold_min Hold_weight]]].
      split; [rewrite Hparent_out_v; exact Hold_in |].
      split; [rewrite Hlow_out_v; exact Hold_low |].
      split.
      * unfold min_object_of_subset in *.
	        destruct Hold_min as [Hold_subset Hold_le].
	        split.
	        -- rewrite Hparent_out_v.
	           left; exact Hold_subset.
	        -- intros e' Hedge'.
	           unfold add_matrix_row_edge_for_vertex in Hedge'.
	           destruct Hedge' as [Hold_edge | [Hvcur _]].
	           ++ rewrite Hparent_out_v.
	              apply Hold_le; exact Hold_edge.
	           ++ contradiction.
	      * rewrite Hparent_out_v.
	        rewrite Hlow_out_v; exact Hold_weight.
    + right.
      split.
      * intros e' Hedge'.
        unfold add_matrix_row_edge_for_vertex in Hedge'.
        destruct Hedge' as [Hold_edge | [Hvcur _]].
        -- exact (Hnone_old e' Hold_edge).
        -- contradiction.
      * rewrite Hlow_out_v; exact Hlow_old.
Qed.

Inductive scan_matrix_row_update
    (g : G) (matrix : list (list Z)) (inf : Z)
    (s : St) (from_v : V)
    : list V -> list Z -> list E -> list Z -> list E -> Prop :=
| scan_matrix_row_update_nil :
    forall lowcost edge_parent,
      scan_matrix_row_update g matrix inf s from_v nil
        lowcost edge_parent lowcost edge_parent
| scan_matrix_row_update_cons :
    forall v rest lowcost0 edge_parent0 lowcost1 edge_parent1 lowcost2 edge_parent2,
      scan_one_matrix_neighbor_update g matrix inf s from_v v
        lowcost0 edge_parent0 lowcost1 edge_parent1 ->
      scan_matrix_row_update g matrix inf s from_v rest
        lowcost1 edge_parent1 lowcost2 edge_parent2 ->
      scan_matrix_row_update g matrix inf s from_v (v :: rest)
        lowcost0 edge_parent0 lowcost2 edge_parent2.

Definition scan_matrix_row_prefix_update
    (g : G) (matrix : list (list Z)) (inf : Z)
    (s : St) (from_v : V)
    (j : Z)
    (lowcost_in : list Z) (edge_parent_in : list E)
    (lowcost_out : list Z) (edge_parent_out : list E) : Prop :=
  scan_matrix_row_update g matrix inf s from_v (Zrange 0 j)
    lowcost_in edge_parent_in lowcost_out edge_parent_out.

Lemma scan_matrix_row_update_lengths :
  forall g matrix inf s from_v scanned
         lowcost_in edge_parent_in lowcost_out edge_parent_out,
    scan_matrix_row_update g matrix inf s from_v scanned
      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
    Zlength lowcost_out = Zlength lowcost_in /\
    Zlength edge_parent_out = Zlength edge_parent_in.
Proof.
  intros g matrix inf s from_v scanned lowcost_in edge_parent_in
         lowcost_out edge_parent_out Hscan.
  induction Hscan.
  - split; reflexivity.
  - destruct (scan_one_matrix_neighbor_update_lengths
      g matrix inf s from_v v lowcost0 edge_parent0 lowcost1 edge_parent1 H)
      as [Hlow1 Hedge1].
    destruct IHHscan as [Hlow2 Hedge2].
    split; lia.
Qed.

Lemma scan_matrix_row_prefix_update_zero :
  forall g matrix inf s from_v lowcost edge_parent,
    scan_matrix_row_prefix_update g matrix inf s from_v 0
      lowcost edge_parent lowcost edge_parent.
Proof.
  intros g matrix inf s from_v lowcost edge_parent.
  unfold scan_matrix_row_prefix_update, Zrange.
  constructor.
Qed.

Definition scan_matrix_row_full_update
    (n : Z) (g : G) (matrix : list (list Z)) (inf : Z)
    (s : St) (from_v : V)
    (lowcost_in : list Z) (edge_parent_in : list E)
    (lowcost_out : list Z) (edge_parent_out : list E) : Prop :=
  scan_matrix_row_prefix_update g matrix inf s from_v n
    lowcost_in edge_parent_in lowcost_out edge_parent_out.

Lemma scan_matrix_row_update_selected_edges_match_state :
  forall g matrix inf src s from_v scanned
         lowcost_in edge_parent_in lowcost_out edge_parent_out,
    selected_edges_match_state g src s edge_parent_in ->
    (forall v,
       In v (graph_vertices g) ->
       0 <= v < Zlength lowcost_in /\
       0 <= v < Zlength edge_parent_in) ->
    (forall cur, In cur scanned -> In cur (graph_vertices g)) ->
    scan_matrix_row_update g matrix inf s from_v scanned
      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
    selected_edges_match_state g src s edge_parent_out.
Proof.
  intros g matrix inf src s from_v scanned lowcost_in edge_parent_in
         lowcost_out edge_parent_out Hparent Hrange Hcur_graph Hscan.
  induction Hscan as
    [lowcost edge_parent
    | cur rest lowcost0 edge_parent0 lowcost1 edge_parent1
      lowcost2 edge_parent2 Hone Hrest IH].
  - exact Hparent.
  - simpl in Hcur_graph.
    assert (Hparent1 :
      selected_edges_match_state g src s edge_parent1).
    {
      eapply scan_one_matrix_neighbor_update_selected_edges_match_state; eauto.
    }
    destruct (scan_one_matrix_neighbor_update_lengths
      g matrix inf s from_v cur lowcost0 edge_parent0 lowcost1 edge_parent1 Hone)
      as [Hlow_len Hparent_len].
    apply IH.
    + exact Hparent1.
    + intros v Hv_graph.
      specialize (Hrange v Hv_graph).
      rewrite Hlow_len, Hparent_len.
      exact Hrange.
    + intros cur' Hcur'.
      apply Hcur_graph. auto.
Qed.

Lemma scan_matrix_row_update_app :
  forall g matrix inf s from_v l1 l2 lowcost0 edge_parent0 lowcost1 edge_parent1 lowcost2 edge_parent2,
    scan_matrix_row_update g matrix inf s from_v l1 lowcost0 edge_parent0 lowcost1 edge_parent1 ->
    scan_matrix_row_update g matrix inf s from_v l2 lowcost1 edge_parent1 lowcost2 edge_parent2 ->
    scan_matrix_row_update g matrix inf s from_v (l1 ++ l2) lowcost0 edge_parent0 lowcost2 edge_parent2.
Proof.
  intros g matrix inf s from_v l1.
  induction l1 as [| v rest IH]; intros l2 lowcost0 edge_parent0 lowcost1 edge_parent1 lowcost2 edge_parent2 H1 H2.
  - inversion H1; subst. exact H2.
  - inversion H1; subst. simpl. econstructor; eauto.
Qed.

Lemma scan_matrix_row_prefix_update_snoc :
  forall g matrix inf s from_v j lowcost0 edge_parent0 lowcost1 edge_parent1 lowcost2 edge_parent2,
    0 <= j ->
    scan_matrix_row_prefix_update g matrix inf s from_v j lowcost0 edge_parent0 lowcost1 edge_parent1 ->
    scan_one_matrix_neighbor_update g matrix inf s from_v j lowcost1 edge_parent1 lowcost2 edge_parent2 ->
    scan_matrix_row_prefix_update g matrix inf s from_v (j + 1) lowcost0 edge_parent0 lowcost2 edge_parent2.
Proof.
  intros g matrix inf s from_v j lowcost0 edge_parent0 lowcost1 edge_parent1 lowcost2 edge_parent2 Hj Hprefix Hone.
  unfold scan_matrix_row_prefix_update in *.
  rewrite Zrange_0_snoc by exact Hj.
  eapply scan_matrix_row_update_app.
  - exact Hprefix.
		  - econstructor; [exact Hone|constructor].
Qed.

Lemma scan_matrix_row_update_lowcost_bound :
  forall n g matrix inf s from_v scanned
         lowcost_in edge_parent_in lowcost_out edge_parent_out,
    adjacency_matrix_model n matrix g inf ->
    0 <= inf ->
    0 <= from_v < n ->
    (forall cur, In cur scanned -> 0 <= cur < n) ->
    Zlength lowcost_in = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k lowcost_in 0 <= inf) ->
    scan_matrix_row_update g matrix inf s from_v scanned
      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
    forall k, 0 <= k < n -> 0 <= Znth k lowcost_out 0 <= inf.
Proof.
  intros n g matrix inf s from_v scanned lowcost_in edge_parent_in
         lowcost_out edge_parent_out Hmodel Hinf Hfrom Hscanned Hlen Hbound Hscan.
  induction Hscan.
  - exact Hbound.
  - assert (Hv_range : 0 <= v < n).
    { apply Hscanned. simpl; auto. }
    assert (Hbound1 :
      forall k, 0 <= k < n -> 0 <= Znth k lowcost1 0 <= inf).
    {
      eapply (scan_one_matrix_neighbor_update_lowcost_bound
        n g matrix inf s from_v v lowcost0 edge_parent0 lowcost1 edge_parent1);
        eauto.
    }
    assert (Hlen1 : Zlength lowcost1 = n).
    {
      pose proof (scan_one_matrix_neighbor_update_lengths
        g matrix inf s from_v v lowcost0 edge_parent0 lowcost1 edge_parent1 H) as [Hlow_len _].
      lia.
    }
    specialize (IHHscan
      (fun cur Hcur => Hscanned cur (or_intror Hcur))
      Hlen1 Hbound1).
    exact IHHscan.
Qed.

Lemma scan_matrix_row_update_lowcost_parent_match_by :
  forall n g matrix inf s from_v scanned
         eligible_vertex edge_for_vertex
         lowcost_in edge_parent_in lowcost_out edge_parent_out,
	    adjacency_matrix_model n matrix g inf ->
	    vvalid s.(Prim.graph_in_state) from_v ->
	    lowcost_parent_match_by
      g eligible_vertex edge_for_vertex
      lowcost_in edge_parent_in inf ->
			    scan_matrix_row_update g matrix inf s from_v scanned
			      lowcost_in edge_parent_in lowcost_out edge_parent_out ->
			    (forall cur, In cur scanned -> In cur (graph_vertices g)) ->
			    (forall cur, In cur scanned ->
			      matrix_entry matrix from_v cur = inf \/
			      matrix_entry matrix from_v cur < inf) ->
		    (forall v, eligible_vertex v -> ~ vvalid s.(Prim.graph_in_state) v) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_in) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_in) ->
    lowcost_parent_match_by
      g eligible_vertex
      (add_matrix_row_edges_for_vertex g s from_v scanned edge_for_vertex)
      lowcost_out edge_parent_out inf.
Proof.
  intros n g matrix inf s from_v scanned.
  induction scanned as [| cur rest IH];
    intros eligible_vertex edge_for_vertex
		           lowcost_in edge_parent_in lowcost_out edge_parent_out
			           Hmodel Hfrom_valid Hmatch Hscan Hcur_graph Hentry_case Helig_out
		           Hlow_range Hparent_range.
  - inversion Hscan; subst.
    simpl.
    exact Hmatch.
  - inversion Hscan as
      [| ? ? lowcost0 edge_parent0 lowcost1 edge_parent1
           lowcost2 edge_parent2 Hone Hrest]; subst.
    simpl.
    assert (Hmatch1 :
      lowcost_parent_match_by
        g eligible_vertex
        (add_matrix_row_edge_for_vertex g s from_v cur edge_for_vertex)
        lowcost1 edge_parent1 inf).
		    {
		      eapply scan_one_matrix_neighbor_update_lowcost_parent_match_by; eauto.
		      - apply Hcur_graph. simpl; auto.
		      - apply Hentry_case. simpl; auto.
		    }
    destruct (scan_one_matrix_neighbor_update_lengths
      g matrix inf s from_v cur lowcost_in edge_parent_in lowcost1 edge_parent1 Hone)
      as [Hlow_len Hparent_len].
	    eapply IH; eauto.
	    + intros cur' Hcur'.
	      apply Hcur_graph. simpl; auto.
	    + intros cur' Hcur'.
	      apply Hentry_case. simpl; auto.
		    + intros v Hv_graph.
	      rewrite Hlow_len.
	      apply Hlow_range; exact Hv_graph.
	    + intros v Hv_graph.
	      rewrite Hparent_len.
	      apply Hparent_range; exact Hv_graph.
Qed.

Lemma scan_matrix_row_full_update_lowcost_parent_match_after_add :
  forall n matrix g inf s s_after lowcost_before edge_parent_before
         lowcost_after edge_parent_after minIndex,
    adjacency_matrix_model n matrix g inf ->
    lowcost_parent_match g s lowcost_before edge_parent_before inf ->
    selected_parent_add_to_mst g s s_after edge_parent_before minIndex ->
    scan_matrix_row_full_update n g matrix inf s_after minIndex
      lowcost_before edge_parent_before lowcost_after edge_parent_after ->
    lowcost_parent_match g s_after lowcost_after edge_parent_after inf.
Proof.
  intros n matrix g inf s s_after lowcost_before edge_parent_before
         lowcost_after edge_parent_after minIndex
         Hmodel Hmatch_before Hadd Hscan_full.
  pose proof (lowcost_parent_match_to_by
    g s lowcost_before edge_parent_before inf Hmatch_before)
    as Hby_old.
  assert (Hby_old_for_after :
    lowcost_parent_match_by
      g
      (fun v => ~ vvalid s_after.(Prim.graph_in_state) v)
      (fun v e => is_cut_edge_to_vertex g s v e)
      lowcost_before edge_parent_before inf).
  {
    eapply lowcost_parent_match_by_iff; [exact Hby_old | |].
    - intros v _ Hvout_after Hv_old.
      apply Hvout_after.
      eapply selected_parent_add_to_mst_old_vvalid; eauto.
    - intros v e _ _; reflexivity.
  }
  destruct Hby_old_for_after as [Harray_range Hbody].
  assert (Hby_old_for_after_full :
    lowcost_parent_match_by
      g
      (fun v => ~ vvalid s_after.(Prim.graph_in_state) v)
      (fun v e => is_cut_edge_to_vertex g s v e)
      lowcost_before edge_parent_before inf)
    by (split; [exact Harray_range | exact Hbody]).
  assert (Hscan_by :
    lowcost_parent_match_by
      g
      (fun v => ~ vvalid s_after.(Prim.graph_in_state) v)
      (add_matrix_row_edges_for_vertex
        g s_after minIndex (Zrange 0 n)
        (fun v e => is_cut_edge_to_vertex g s v e))
      lowcost_after edge_parent_after inf).
  {
    unfold scan_matrix_row_full_update, scan_matrix_row_prefix_update in Hscan_full.
    eapply scan_matrix_row_update_lowcost_parent_match_by
      with (n := n)
           (lowcost_in := lowcost_before)
           (edge_parent_in := edge_parent_before); eauto.
	    - eapply selected_parent_add_to_mst_minIndex_vvalid; eauto.
			    - intros cur Hcur.
				      apply adjacency_matrix_vertex_in_graph
				        with (n := n) (matrix := matrix) (g := g) (inf := inf); auto.
		      rewrite <- In_Zrange in Hcur.
		      exact Hcur.
		    - intros cur Hcur.
		      rewrite <- In_Zrange in Hcur.
		      assert (Hmin_range : 0 <= minIndex < n).
		      {
		        assert (Hmin_graph : In minIndex (graph_vertices g)).
		        {
		          destruct Hadd as [u [v [Hpair _]]].
		          unfold selected_parent_pair in Hpair.
		          destruct Hpair as [-> [_ [_ Hstep]]].
		          change (vvalid g minIndex).
		          eapply step_vvalid2; eauto.
		        }
			        pose proof Hmodel as Hmodel_vertices.
			        unfold adjacency_matrix_model in Hmodel_vertices.
			        destruct Hmodel_vertices as [_ [Hvertices _]].
			        apply Hvertices in Hmin_graph.
			        rewrite <- In_Zrange in Hmin_graph.
			        exact Hmin_graph.
			      }
		      pose proof Hmodel as Hmodel_entry.
		      unfold adjacency_matrix_model in Hmodel_entry.
		      destruct Hmodel_entry as [_ [_ [Hentry _]]].
		      destruct (Hentry minIndex cur Hmin_range Hcur) as [Hno_edge | [_ Hlt]].
		      + left; exact Hno_edge.
		      + right; exact Hlt.
			    - intros v Hv.
			      exact (proj1 (Harray_range v Hv)).
    - intros v Hv.
      exact (proj2 (Harray_range v Hv)).
  }
  apply lowcost_parent_match_by_to.
  eapply lowcost_parent_match_by_iff; [exact Hscan_by | |].
  - intros v _ Hvout; exact Hvout.
	  - intros v e Hv_graph Hvout_after.
	    rewrite add_matrix_row_edges_for_vertex_iff.
	    apply (is_cut_edge_to_vertex_after_add_row_iff
		      n matrix g inf s s_after edge_parent_before minIndex v e); eauto.
Qed.

Lemma initSt_row_edges_for_vertex_iff :
  forall n matrix g inf src v e,
    adjacency_matrix_model n matrix g inf ->
    src = 0 ->
    In v (graph_vertices g) ->
    ~ vvalid (Prim.graph_in_state (initSt g src)) v ->
    add_matrix_row_edges_for_vertex
      g (initSt g src) src (Zrange 0 n)
      (fun _ _ => False) v e <->
    is_cut_edge_to_vertex g (initSt g src) v e.
Proof.
  intros n matrix g inf src v e Hmodel Hsrc Hv_graph Hvout.
  rewrite add_matrix_row_edges_for_vertex_iff.
  split.
  - intros [Hfalse | [_ Hrow]]; [contradiction | apply Hrow].
  - intros Hcut.
    right.
    split.
    {
      unfold adjacency_matrix_model in Hmodel.
      destruct Hmodel as [_ [Hvertices _]].
      rewrite <- Hvertices.
      exact Hv_graph.
    }
    unfold matrix_row_edge_for_vertex.
    split; [exact Hcut |].
    unfold is_cut_edge_to_vertex in Hcut.
    destruct Hcut as [_ [_ [u [w [Hu [_ Hstep]]]]]].
    rewrite initSt_vvalid in Hu.
    subst u.
    unfold step_aux, graph_instance, graph_step in Hstep.
    simpl in Hstep.
    destruct Hstep as [_ [_ Hendpoints]].
    unfold edge_src, edge_dst in *.
    destruct e as [a b]; simpl in *.
    destruct Hendpoints as [[Ha Hb] | [Ha Hb]]; subst; simpl; auto.
Qed.

Lemma initSt_lowcost_parent_match_by_empty :
  forall n matrix g inf src,
    adjacency_matrix_model n matrix g inf ->
    src = 0 ->
    2 <= n ->
    lowcost_parent_match_by
      g
      (fun v => ~ vvalid (Prim.graph_in_state (initSt g src)) v)
      (fun _ _ => False)
      (replace_Znth src 0 (repeat_Z inf n))
      (default_edge_list n)
      inf.
Proof.
  intros n matrix g inf src Hmodel Hsrc Hn.
  split.
  - intros v Hv_graph.
    assert (Hv_range : 0 <= v < n).
    {
      unfold adjacency_matrix_model in Hmodel.
      destruct Hmodel as [_ [Hvertices _]].
      apply Hvertices in Hv_graph.
      rewrite <- In_Zrange in Hv_graph.
      exact Hv_graph.
    }
    split.
    + subst src.
      rewrite Zlength_replace_Znth_local
        by (unfold repeat_Z; rewrite Zlength_correct, repeat_length; lia).
      unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
    + unfold default_edge_list.
      rewrite Zlength_correct, repeat_length. lia.
  - intros v Hv_graph Hvout.
    right.
    split.
    + intros e Hfalse. exact Hfalse.
    + assert (Hv_range : 0 <= v < n).
      {
        unfold adjacency_matrix_model in Hmodel.
        destruct Hmodel as [_ [Hvertices _]].
        apply Hvertices in Hv_graph.
        rewrite <- In_Zrange in Hv_graph.
        exact Hv_graph.
      }
      assert (Hv_neq_src : v <> src).
      {
        intros ->.
        apply Hvout.
        rewrite initSt_vvalid.
        reflexivity.
      }
      subst src.
      rewrite Znth_replace_Znth_diff_local.
      * unfold repeat_Z.
        rewrite Znth_repeat_lt by lia.
        reflexivity.
      * unfold repeat_Z.
        rewrite Zlength_correct, repeat_length. lia.
      * unfold repeat_Z.
        rewrite Zlength_correct, repeat_length. lia.
      * congruence.
Qed.

Lemma scan_matrix_row_full_update_lowcost_parent_match_init :
  forall n matrix g inf src lowcost_after edge_parent_after,
    adjacency_matrix_model n matrix g inf ->
    src = 0 ->
    2 <= n ->
    scan_matrix_row_full_update n g matrix inf (initSt g src) src
      (replace_Znth src 0 (repeat_Z inf n))
      (default_edge_list n)
      lowcost_after edge_parent_after ->
    lowcost_parent_match g (initSt g src)
      lowcost_after edge_parent_after inf.
Proof.
  intros n matrix g inf src lowcost_after edge_parent_after
         Hmodel Hsrc Hn Hscan.
  pose proof (initSt_lowcost_parent_match_by_empty
    n matrix g inf src Hmodel Hsrc Hn) as Hinit_by.
  assert (Hscan_by :
    lowcost_parent_match_by
      g
      (fun v => ~ vvalid (Prim.graph_in_state (initSt g src)) v)
      (add_matrix_row_edges_for_vertex
        g (initSt g src) src (Zrange 0 n) (fun _ _ => False))
      lowcost_after edge_parent_after inf).
  {
    unfold scan_matrix_row_full_update, scan_matrix_row_prefix_update in Hscan.
    eapply scan_matrix_row_update_lowcost_parent_match_by
      with
        (n := n)
        (matrix := matrix)
        (from_v := src)
        (scanned := Zrange 0 n)
        (lowcost_in := replace_Znth src 0 (repeat_Z inf n))
        (edge_parent_in := default_edge_list n); eauto.
    - rewrite initSt_vvalid. reflexivity.
    - intros cur Hcur.
      rewrite <- In_Zrange in Hcur.
      eapply adjacency_matrix_vertex_in_graph; eauto.
    - intros cur Hcur.
      rewrite <- In_Zrange in Hcur.
      unfold adjacency_matrix_model in Hmodel.
      destruct Hmodel as [_ [_ [Hentry _]]].
      subst src.
      destruct (Hentry 0 cur ltac:(lia) Hcur) as [Hinf | [_ Hlt]].
      + left; exact Hinf.
      + right; exact Hlt.
    - intros v Hv_graph.
      exact (proj1 (proj1 Hinit_by v Hv_graph)).
    - intros v Hv_graph.
      exact (proj2 (proj1 Hinit_by v Hv_graph)).
  }
  apply lowcost_parent_match_by_to.
  eapply lowcost_parent_match_by_iff; [exact Hscan_by | |].
  - intros v Hv_graph Hvout. exact Hvout.
  - intros v e Hv_graph Hvout.
    apply (initSt_row_edges_for_vertex_iff
      n matrix g inf src v e); eauto.
Qed.
