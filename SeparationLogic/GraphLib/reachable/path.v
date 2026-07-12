Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Arith.Arith.
Require Import ListLib.Base.Positional.
From GraphLib Require Import graph_basic Syntax.
From ListLib Require Import Base.Inductive.

Import ListNotations.

Record vpath_iff_epath_prop
    {G V E: Type}
    `{pg: Graph G V E}
    `{gv: GValid G}
    (g: G)
    (pv: list V)
    (pe: list E): Prop := {
    vpath_iff_epath_length: length pv = length pe + 1;
    vpath_iff_epath_step:
        forall n u v e, 0 <= n < length pe ->
            nth_error pe n = Some e ->
            nth_error pv n = Some u ->
            nth_error pv (S n) = Some v ->
            step_aux g e u v;
}.

Class Path 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) := {
    path_valid: 
        G -> P -> Prop; 
    vertex_in_path: 
        P -> list V;
    head: 
        P -> V;
    head_valid: 
        forall g p, path_valid g p -> 
            Some (head p) = hd_error (vertex_in_path p);
    tail: 
        P -> V;
    tail_valid: 
        forall g p, path_valid g p -> 
            Some (tail p) = tl_error (vertex_in_path p);
    edge_in_path: 
        P -> list E;
    vpath_iff_epath:
        forall g p, path_valid g p ->
            vpath_iff_epath_prop g (vertex_in_path p) (edge_in_path p);
}.

Class EmptyPath 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) := {
    empty_path: V -> P;
    empty_path_valid: forall g v, path_valid g (empty_path v);
    empty_path_vertex: forall v, vertex_in_path (empty_path v) = [v];
}.

Class SinglePath 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) := {
    single_path: V -> V -> E -> P;
    single_path_valid: forall g u v e, step_aux g e u v -> path_valid g (single_path u v e);
    single_path_vertex: forall u v e, vertex_in_path (single_path u v e) = [u; v];
    single_path_edge: forall u v e, edge_in_path (single_path u v e) = [e];
}.

Class ConcatPath 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) := {
    concat_path: P -> P -> P;

    concat_path_valid: forall g a1 a2, 
    path_valid g a1 -> path_valid g a2 -> 
    tail a1 = head a2 -> 
    path_valid g (concat_path a1 a2);

    concat_path_vertex: forall a1 a2, vertex_in_path (concat_path a1 a2) = vertex_in_path a1 ++ (tl (vertex_in_path a2));

    concat_path_edge: forall a1 a2, edge_in_path (concat_path a1 a2) = edge_in_path a1 ++ edge_in_path a2;
}.

Inductive PathConsView {P E V: Type} :=
| DestructBase1n (v: V)               
| DestructStep1n (p: P) (u v: V) (e: E). 

Definition path_cons_spec 
  {G V E P: Type} 
  `{pg: Graph G V E} 
  `{gv: GValid G} 
  {p: Path G V E P} 
  {ep: EmptyPath G V E P p} 
  {sp: SinglePath G V E P p} 
  {cp: ConcatPath G V E P p} 
  (g: G) (p: P) (d: PathConsView) : Prop :=
  match d with 
  | DestructBase1n v => 
      p = empty_path v
  | DestructStep1n p' u v e =>
      path_valid g p' /\
      head p' = v /\
      step_aux g e u v /\
      p = concat_path (single_path u v e) p'
  end.

Class Destruct1nPath 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) 
    (ep: EmptyPath G V E P p) 
    (sp: SinglePath G V E P p) 
    (cp: ConcatPath G V E P p):= {
    destruct_1n_path: forall g p, path_valid g p -> @PathConsView P E V;
    
    destruct_1n_spec: forall g p (Hvalid: path_valid g p),
        path_cons_spec g p (destruct_1n_path g p Hvalid);
}.

Inductive PathSnocView {P E V: Type} :=
| DestructBasen1 (v: V)
| DestructStepn1 (p: P) (u v: V) (e: E). 


Definition path_snoc_spec 
  {G V E P: Type} 
  `{pg: Graph G V E} 
  `{gv: GValid G} 
  {p: Path G V E P} 
  {ep: EmptyPath G V E P p} 
  {sp: SinglePath G V E P p} 
  {cp: ConcatPath G V E P p} 
  (g: G) (p: P) (d: PathSnocView) : Prop :=
  match d with
  | DestructBasen1 v =>
      p = empty_path v
  | DestructStepn1 p' u v e =>
      path_valid g p' /\
      tail p' = u /\
      step_aux g e u v /\
      p = concat_path p' (single_path u v e)
  end.

Class Destructn1Path 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) 
    (ep: EmptyPath G V E P p) 
    (sp: SinglePath G V E P p) 
    (cp: ConcatPath G V E P p) := {
    destruct_n1_path: forall g p, path_valid g p -> @PathSnocView P E V;
    destruct_n1_spec: forall g p (Hvalid: path_valid g p),
        path_snoc_spec g p (destruct_n1_path g p Hvalid);
}.

(* Type -> Prop ? *)
Class PathInd1n 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) 
    (ep: EmptyPath G V E P p) 
    (sp: SinglePath G V E P p) 
    (cp: ConcatPath G V E P p) := {
    path_ind1n: forall g (X: P -> Type) 
    (H1: forall v, X (empty_path v)) 
    (H2: forall u v e a2, 
    step_aux g e u v -> 
    path_valid g a2 ->
    head a2 = v ->
    X a2 -> 
    X (concat_path (single_path u v e) a2)), 
    forall a, path_valid g a -> X a;
}.

Class PathIndn1 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) 
    (ep: EmptyPath G V E P p) 
    (sp: SinglePath G V E P p) 
    (cp: ConcatPath G V E P p) := {
    path_indn1: forall g (X: P -> Type) 
    (H1: forall v, X (empty_path v)) 
    (H2: forall u v e a1, step_aux g e u v -> 
    path_valid g a1 ->
    tail a1 = u ->
    X a1 -> 
    X (concat_path a1 (single_path u v e))), 
    forall a, path_valid g a -> X a;
}.

(* 外延性。如果两个Path类型的顶点列表和边列表相同，那么它们是完全相同。 *)
(* 事实上我们已经能够得到它们的各种接口相同。为什么还需要它们本身相同？ *)
(* 不一定需要vertex也相同。 *)
Class PathExtensionality 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) := {
    path_ext: forall g p1 p2,
        path_valid g p1 -> path_valid g p2 -> 
        head p1 = head p2 ->
        edge_in_path p1 = edge_in_path p2 ->
        p1 = p2
}.

Lemma Some_inversion {A: Type}: 
    forall (x y: A), Some x = Some y -> x = y.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Lemma Some_injection {A: Type}: 
    forall (x y: A), x = y -> Some x = Some y.
Proof.
  intros.
  subst.
  reflexivity.
Qed.







(*
====================================================================
          1n-Side (Cons-style)           n1-Side (Snoc-style)
====================================================================

       Destruct1nPath  <---------------  PathIndn1
           ^    |           (3)           ^    |
           |    |                         |    |
       (1) |    | (2)                 (2) |    | (1)
           |    v           (3)           |    v
         PathInd1n    ------------>   Destructn1Path

--------------------------------------------------------------------
推导逻辑说明：
(1) [Length Induction]: 通过路径长度的良序性 (well-founded)，由分解式
    推导出归纳原理。
(2) [Sigma Construction]: 通过归纳原理构造 Sigma 类型，提取出对应的
    分解式及证明。
(3) [Structural Rewrite]: (PathInd1n + PathExt) -> Destructn1Path
    利用 1n 归纳结合结合律 (Assoc) 与单位元 (Id)，将前置路径重新
    包装为后置路径结构。这是跨维度的核心。
(4) [Mutual Equivalence]: 只要其中一侧的 Ind 和 Destruct 确立，且具备
    外延性 (PathExt)，四个维度即可实现全等价互推。
====================================================================
*)







Section DERIVATION.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}.

(* 所有的路径顶点集合都不为空 *)
Theorem path_valid_vertex_not_nil: forall g p,
  path_valid g p ->
  vertex_in_path p <> nil.
Proof.
  intros.
  pose proof vpath_iff_epath g p H. 
  destruct H0 as [contra _]. 
  unfold not; intros; rewrite H0 in contra. 
  simpl in contra. 
  lia.
Qed.

(* empty_path的边列表为空 *)
Theorem empty_path_edge: forall (g: G) v,
  edge_in_path (empty_path v) = nil. 
Proof.
  intros. 
  pose proof (vpath_iff_epath g (empty_path v) (empty_path_valid g v)) as [Hlen _].
  rewrite empty_path_vertex in Hlen.
  simpl in Hlen.
  assert (length (edge_in_path (empty_path v)) = 0%nat) by lia.
  rewrite length_zero_iff_nil in H. 
  auto.
Qed.

(* ============================================================ *)
(*                  Destruct1nPath -> PathInd1n                 *)
(* ============================================================ *)
#[export] Instance Destruct1n2PathInd1n 
    {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath} : 
    PathInd1n G V E P path emptypath singlepath concatpath.
Proof.
  constructor.
  intros g X H1 H2 a Ha.
  remember (length (edge_in_path a)) as n.
  revert a Ha Heqn.
  refine (well_founded_induction_type lt_wf
  (fun n => forall a, path_valid g a -> n = length (edge_in_path a) -> X a) _ n). 
  intros k IH a Ha Heqn.
  pose proof (destruct_1n_spec g a Ha) as Hspec. 
  unfold path_cons_spec in Hspec.
  destruct (destruct_1n_path g a Ha) eqn: ?.
  - subst a. apply H1.
  - destruct Hspec as [Hvalid_rest [Hhead [Hstep Heq]]].
    subst a.
    apply H2; auto.
    + assert (Hlt: length (edge_in_path p) < k).
      { subst k.
        rewrite concat_path_edge, single_path_edge. simpl. lia. }
      specialize (IH _ Hlt p Hvalid_rest eq_refl).
      exact IH.
Qed.

(* ============================================================ *)
(*                  Destructn1Path -> PathIndn1                 *)
(* ============================================================ *)
#[export] Instance Destructn12PathIndn1 
    {destructn1path: Destructn1Path G V E P path emptypath singlepath concatpath} : 
    PathIndn1 G V E P path emptypath singlepath concatpath.
Proof.
  constructor.
  intros g X H1 H2 a Ha.
  remember (length (edge_in_path a)) as n.
  revert a Ha Heqn.
  refine (well_founded_induction_type lt_wf
  (fun n => forall a, path_valid g a -> n = length (edge_in_path a) -> X a) _ n). 
  intros k IH a Ha Heqn.
  pose proof (destruct_n1_spec g a Ha) as Hspec.
  unfold path_snoc_spec in Hspec.
  destruct (destruct_n1_path g a Ha) eqn: ?.
  - subst a. apply H1.
  - destruct Hspec as [Hvalid_prev [Htail [Hstep Heq]]].
    subst a.
    apply H2; auto.
    + assert (Hlt: length (edge_in_path p) < k).
      { subst k.
        rewrite concat_path_edge, single_path_edge. 
        rewrite length_app. simpl. lia. }
      specialize (IH _ Hlt p Hvalid_prev eq_refl).
      exact IH.
Qed.

Definition build_1npath_via_ind1n 
  {ind1n: PathInd1n G V E P path emptypath singlepath concatpath}
  (g: G) (p: P) (H: path_valid g p)  : 
  { d : PathConsView | path_cons_spec g p d }.
Proof.
  revert p H.
  apply (path_ind1n g (fun p => { d : PathConsView | path_cons_spec g p d })).
  - intros v.
    exists (DestructBase1n v).
    simpl. reflexivity.
  - intros u v e a2 Hstep Hvalid_a2 Hhead_a2 IH_a2.
    exists (DestructStep1n a2 u v e).
    simpl.
    repeat split; auto.
Defined.

(* ============================================================ *)
(*                  PathInd1n -> Destruct1nPath                 *)
(* ============================================================ *)
#[export] Instance PathInd1n2Destruct1nPath 
    {pathind1n: PathInd1n G V E P path emptypath singlepath concatpath} : 
    Destruct1nPath G V E P path emptypath singlepath concatpath.
Proof.
  unshelve econstructor.
  - intros g p Hvalid.
    exact (proj1_sig (build_1npath_via_ind1n g p Hvalid)).
  - intros g p Hvalid.
    pose proof (proj2_sig (build_1npath_via_ind1n g p Hvalid)) as Hspec.
    exact Hspec.
Qed.


Definition build_n1path_via_indn1 
  {indn1: PathIndn1 G V E P path emptypath singlepath concatpath}
  (g: G) (p: P) (H: path_valid g p) : 
  { d : PathSnocView | path_snoc_spec g p d }.
Proof.
  revert p H.
  apply (path_indn1 g (fun p => { d : PathSnocView | path_snoc_spec g p d })).
  - intros v.
    exists (DestructBasen1 v).
    simpl. reflexivity.
  - intros u v e a1 Hstep Hvalid_a1 Htail_a1 IH_a1.
    exists (DestructStepn1 a1 u v e).
    simpl.
    repeat split; auto.
Defined.

(* ============================================================ *)
(*                  PathIndn1 -> Destructn1Path                 *)
(* ============================================================ *)
#[export] Instance PathIndn12Destructn1Path 
    {pathindn1: PathIndn1 G V E P path emptypath singlepath concatpath} : 
    Destructn1Path G V E P path emptypath singlepath concatpath.
Proof.
  unshelve econstructor.
  - intros g p Hvalid.
    exact (proj1_sig (build_n1path_via_indn1 g p Hvalid)).
  - intros g p Hvalid.
    exact (proj2_sig (build_n1path_via_indn1 g p Hvalid)).
Qed.

Theorem path_concat_head_elim: 
  forall g p1 p2, 
  path_valid g p1 -> path_valid g p2 ->
  tail p1 = head p2 ->
  head (concat_path p1 p2) = head p1.
Proof.
  intros.
  apply Some_inversion.
  erewrite head_valid; eauto.
  - rewrite concat_path_vertex. 
    destruct (vertex_in_path p1) eqn:Hv1.
    * apply path_valid_vertex_not_nil in H. 
      congruence.
    * erewrite head_valid; eauto. 
      rewrite Hv1. reflexivity.
  - eapply concat_path_valid; eauto.
Qed. 

Theorem path_concat_tail_elim: 
  forall g p1 p2, 
  path_valid g p1 -> path_valid g p2 ->
  tail p1 = head p2 ->
  tail (concat_path p1 p2) = tail p2.
Proof.
  intros.
  apply Some_inversion.
  erewrite tail_valid; eauto.
  - rewrite concat_path_vertex. 
    destruct (vertex_in_path p2) eqn:Hv1.
    * apply path_valid_vertex_not_nil in H0. 
      congruence.
    * erewrite tail_valid; eauto. 
      rewrite Hv1. simpl. 
      destruct (list_snoc_destruct l) as [|[? []]]; subst.
      + apply Some_injection in H1. 
        erewrite tail_valid in H1; eauto. 
        erewrite head_valid in H1; eauto. 
        rewrite Hv1 in H1. 
        rewrite app_nil_r. 
        rewrite H1. 
        reflexivity.
      + rewrite !app_comm_cons. 
        rewrite app_assoc. 
        rewrite !tl_error_last. 
        reflexivity.
  - eapply concat_path_valid; eauto.
Qed.

Theorem path_concat_assoc
  {path_extensionality: PathExtensionality G V E P path}: 
  forall g a b c 
    (Ha: path_valid g a) (Hb: path_valid g b) (Hc: path_valid g c)
    (Hab: tail a = head b) (Hbc: tail b = head c),
    concat_path (concat_path a b) c = concat_path a (concat_path b c).
Proof.
  intros.
  eapply path_ext; eauto.
  - eapply concat_path_valid; eauto;  
    [eapply concat_path_valid; eauto|erewrite path_concat_tail_elim; eauto]. 
  - eapply concat_path_valid; eauto; 
    [eapply concat_path_valid; eauto|erewrite path_concat_head_elim; eauto]. 
  - apply Some_inversion. 
    erewrite !head_valid; eauto.
    + rewrite !concat_path_vertex. 
      rewrite <- !app_assoc.  
      destruct (vertex_in_path b) eqn: Hvb. 
      * apply path_valid_vertex_not_nil in Hb. 
        congruence.
      * reflexivity. 
    + eapply concat_path_valid; eauto.
      * eapply concat_path_valid; eauto.
      * rewrite Hab. 
        erewrite path_concat_head_elim; eauto.
    + eapply concat_path_valid; eauto. 
      * eapply concat_path_valid; eauto.
      * rewrite <- Hbc. 
        erewrite path_concat_tail_elim; eauto.
  - rewrite !concat_path_edge. 
    rewrite <- !app_assoc. 
    reflexivity. 
Qed.

Theorem path_concat_id_l 
  {path_extensionality: PathExtensionality G V E P path}: 
  forall g p, 
  path_valid g p ->
  concat_path (empty_path (head p)) p = p.
Proof.
  intros.
  eapply path_ext; eauto.
  - eapply concat_path_valid; eauto. 
    * apply empty_path_valid.
    * apply Some_inversion. 
      erewrite (tail_valid g); eauto. 
      + rewrite empty_path_vertex. reflexivity.
      + apply empty_path_valid. 
  - apply Some_inversion. 
    erewrite !head_valid; eauto.
    + 
  
  
   erewrite concat_path_vertex; eauto. 
    rewrite empty_path_vertex. 
    destruct (vertex_in_path p) eqn: Hvp.
    * apply path_valid_vertex_not_nil in H. 
      congruence.
    * simpl; f_equal; auto. 
      apply Some_inversion. 
      erewrite head_valid; eauto. 
      rewrite Hvp. 
      reflexivity. 
    + eapply concat_path_valid; eauto.
      * apply empty_path_valid.
      * apply Some_inversion.
        erewrite head_valid; eauto.
        erewrite (tail_valid g); [|eapply empty_path_valid].
        rewrite empty_path_vertex. 
        apply Some_inversion. 
        erewrite <- head_valid; eauto.
  - erewrite concat_path_edge; eauto. 
    erewrite empty_path_edge; eauto. 
Qed. 


Theorem path_concat_id_r 
  {path_extensionality: PathExtensionality G V E P path}: 
  forall g p, 
  path_valid g p ->
  concat_path p (empty_path (tail p)) = p.
Proof.
  intros.
  eapply path_ext; eauto.
  - eapply concat_path_valid; eauto. 
    * apply empty_path_valid. 
    * apply Some_inversion. 
      erewrite (head_valid g); eauto. 
      + rewrite empty_path_vertex. reflexivity.
      + apply empty_path_valid. 
  - apply Some_inversion. 
    erewrite !head_valid; eauto. 
    * erewrite concat_path_vertex; eauto. 
      rewrite empty_path_vertex. 
      rewrite app_nil_r. 
      reflexivity. 
    * eapply concat_path_valid; eauto. 
      + apply empty_path_valid.
      + apply Some_inversion.
        erewrite (head_valid g); [|eapply empty_path_valid].
        rewrite empty_path_vertex. 
        reflexivity.
  - erewrite concat_path_edge; eauto. 
    erewrite empty_path_edge; eauto. 
    apply app_nil_r. 
Qed. 

Definition build_n1path_via_ind1n 
  (g: G) (p: P) (H: path_valid g p) 
  {ind1npath: PathInd1n G V E P path emptypath singlepath concatpath}
  {path_extensionality: PathExtensionality G V E P path} : 
  { d : PathSnocView | path_snoc_spec g p d }.
Proof.
  revert p H.
  apply (path_ind1n g (fun p => { d : PathSnocView | path_snoc_spec g p d })).
  1: { intros v; exists (DestructBasen1 v); reflexivity. }
  intros u v e a2 Hstep Hvalid_a2 Hhead_a2 IH.
  destruct IH as [d_a2 Hspec_a2].
  
  assert (H_single_head: head (single_path u v e) = u). {
    apply Some_inversion.
    erewrite (head_valid g); [|apply single_path_valid; auto].
    rewrite single_path_vertex. reflexivity. }
  assert (H_single_tail: tail (single_path u v e) = v). {
    apply Some_inversion.
    erewrite (tail_valid g); [|apply single_path_valid; auto].
    rewrite single_path_vertex. reflexivity. }

  destruct d_a2 as [v_base | p_prefix u' v' e'].
  
  - simpl in Hspec_a2. subst a2.
    
    assert (v = v_base). {
      pose proof (head_valid g (empty_path v_base) (empty_path_valid g v_base)).
      rewrite empty_path_vertex in H. simpl in H. 
      injection H as H.
      rewrite H in Hhead_a2. congruence.
    } subst v_base.

    exists (DestructStepn1 (empty_path u) u v e).
    simpl. repeat split; auto.
    * apply empty_path_valid.
    * apply Some_inversion.
      erewrite (tail_valid g); [|apply empty_path_valid].
      rewrite empty_path_vertex. reflexivity.
    * rewrite <- H_single_tail at 2. 
      erewrite path_concat_id_r; [|apply single_path_valid; eauto].
      rewrite <- H_single_head at 2.
      erewrite path_concat_id_l; [|apply single_path_valid; eauto]. 
      reflexivity.

  - simpl in Hspec_a2.
    destruct Hspec_a2 as [Hp_valid [Hp_tail [Hp_step Heq_a2]]].
    subst a2.
    assert (H_head_prefix: v = head p_prefix). {
      rewrite <- Hhead_a2.
      erewrite path_concat_head_elim; eauto.
      apply single_path_valid; auto. 
      rewrite Hp_tail.
      apply Some_inversion. 
      erewrite head_valid; [|eapply single_path_valid; eauto]. 
      rewrite single_path_vertex. 
      reflexivity. }
    
    exists (DestructStepn1 (concat_path (single_path u v e) p_prefix) u' v' e').
    simpl. repeat split; auto.
    * apply concat_path_valid; auto.
      + apply single_path_valid; auto.
      + rewrite H_single_tail. auto.
    * erewrite path_concat_tail_elim; eauto.
      + apply single_path_valid; auto.
      + rewrite H_single_tail. auto.
    * erewrite path_concat_assoc; eauto.
      + apply single_path_valid; auto.
      + apply single_path_valid; auto.
      + rewrite H_single_tail. auto. 
      + rewrite Hp_tail.
        apply Some_inversion. 
        erewrite head_valid; [|eapply single_path_valid; eauto]. 
        rewrite single_path_vertex. 
        reflexivity.
Defined.

(* ============================================================ *)
(*                  PathInd1n -> Destructn1Path                 *)
(* ============================================================ *)
#[export] Instance PathInd1n2Destructn1Path 
    {ind1npath: PathInd1n G V E P path emptypath singlepath concatpath}
    {path_extensionality: PathExtensionality G V E P path} : 
    Destructn1Path G V E P path emptypath singlepath concatpath.
Proof.
  unshelve econstructor.
  - intros g p Hvalid.
    exact (proj1_sig (build_n1path_via_ind1n g p Hvalid)).
  - intros g p Hvalid.
    exact (proj2_sig (build_n1path_via_ind1n g p Hvalid)).
Qed.

Definition build_1npath_via_indn1 
  (g: G) (p: P) (H: path_valid g p) 
  {indn1path: PathIndn1 G V E P path emptypath singlepath concatpath}
  {path_extensionality: PathExtensionality G V E P path} : 
  { d : PathConsView | path_cons_spec g p d }.
Proof.
  revert p H.
  apply (path_indn1 g (fun p => { d : PathConsView | path_cons_spec g p d })).
  1: { intros v; exists (DestructBase1n v); reflexivity. }
  intros u v e a1 Hstep Hvalid_a1 Htail_a1 IH.
  destruct IH as [d_a1 Hspec_a1].

  assert (H_single_head: head (single_path u v e) = u). {
    apply Some_inversion.
    erewrite (head_valid g); [|apply single_path_valid; auto].
    rewrite single_path_vertex. reflexivity. }
  assert (H_single_tail: tail (single_path u v e) = v). {
    apply Some_inversion.
    erewrite (tail_valid g); [|apply single_path_valid; auto].
    rewrite single_path_vertex. reflexivity. }

  destruct d_a1 as [v_base | p_rest u' v' e'].

  - simpl in Hspec_a1. subst a1.
    assert (v_base = u). {
      pose proof (tail_valid g (empty_path v_base) (empty_path_valid g v_base)).
      rewrite empty_path_vertex in H.
      injection H as H.
      rewrite Htail_a1 in H; auto. } subst v_base.

    exists (DestructStep1n (empty_path v) u v e).
    simpl. repeat split; auto.
    * apply empty_path_valid.
    * apply Some_inversion.
      erewrite (head_valid g); [|apply empty_path_valid].
      rewrite empty_path_vertex. reflexivity.
    * rewrite <- H_single_head at 1.
      erewrite path_concat_id_l; [|apply single_path_valid; eauto].
      rewrite <- H_single_tail at 3.
      erewrite path_concat_id_r; [|apply single_path_valid; eauto].
      reflexivity.

  - simpl in Hspec_a1.
    destruct Hspec_a1 as [Hp_valid [Hhead_p [Hstep0 Heq_a1]]].
    subst a1.

    assert (H_tail_rest: tail p_rest = u). {
      rewrite <- Htail_a1.
      erewrite path_concat_tail_elim; eauto. 
      apply single_path_valid; auto.
      apply Some_inversion. 
      erewrite tail_valid; [|apply single_path_valid; eauto]. 
      rewrite single_path_vertex.
      rewrite Hhead_p. 
      reflexivity. }

    exists (DestructStep1n (concat_path p_rest (single_path u v e)) u' v' e').
    simpl. repeat split; auto.
    * apply concat_path_valid; auto.
      + apply single_path_valid; auto. 
      + rewrite H_tail_rest. 
        apply Some_inversion. 
        erewrite head_valid; [|eapply single_path_valid; eauto]. 
        rewrite single_path_vertex. 
        reflexivity. 
    * erewrite path_concat_head_elim; eauto.
      + apply single_path_valid; auto.
      + rewrite H_single_head. auto.
    * symmetry.
      erewrite path_concat_assoc; eauto.
      + apply single_path_valid; auto.
      + apply single_path_valid; auto.
      + apply Some_inversion. 
        erewrite tail_valid; [|apply single_path_valid; eauto]. 
        rewrite single_path_vertex. 
        rewrite Hhead_p. 
        reflexivity. 

      + rewrite H_tail_rest.
        rewrite H_single_head. 
        reflexivity.
Defined.

(* ============================================================ *)
(*                  PathIndn1 -> Destruct1nPath                 *)
(* ============================================================ *)
#[export] Instance PathIndn12Destruct1nPath 
    {indn1path: PathIndn1 G V E P path emptypath singlepath concatpath}
    {path_extensionality: PathExtensionality G V E P path} : 
    Destruct1nPath G V E P path emptypath singlepath concatpath.
Proof.
  unshelve econstructor.
  - intros g p Hvalid.
    exact (proj1_sig (build_1npath_via_indn1 g p Hvalid)).
  - intros g p Hvalid.
    exact (proj2_sig (build_1npath_via_indn1 g p Hvalid)).
Qed.

End DERIVATION.
