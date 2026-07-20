Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.reachable.epath.
Require Import GraphLib.reachable.path.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass. 
From ListLib Require Import General.NoDup.
(* g1 is the subgraph of g2 *)
Definition subgraph 
  {G1 G2 V E: Type} 
  {pg1: Graph G1 V E} 
  {pg2: Graph G2 V E} 
  (g1: G1) (g2: G2) : Prop :=
  (forall x y e, step_aux g1 e x y -> step_aux g2 e x y).

Record subgraph2 
  {G1 G2 V E: Type} 
  {pg1: Graph G1 V E} 
  {pg2: Graph G2 V E} 
  (g1: G1) (g2: G2) : Prop := {
  subgraph2_vertex: forall x, vvalid g1 x -> vvalid g2 x;
  subgraph2_step_aux: forall x y e, step_aux g1 e x y -> step_aux g2 e x y;
}.

Record subgraph_vertex_eq
  {G1 G2 V E: Type} 
  {pg1: Graph G1 V E} 
  {pg2: Graph G2 V E} 
  (g1: G1) (g2: G2) : Prop := {
  subgraph_vertex: forall x, vvalid g1 x <-> vvalid g2 x;
  subgraph_step_aux: forall x y e, step_aux g1 e x y -> step_aux g2 e x y;
  }.

Record addEdge {G1 G2 V E: Type} {pg1: Graph G1 V E} {pg2: Graph G2 V E} 
  (g1: G1) (g2: G2) (u v: V) (e: E): Prop := { 
  addEdge_vvalid: forall x, vvalid g2 x <-> vvalid g1 x \/ x = u \/ x = v;
  addEdge_evalid: forall a, evalid g2 a <-> evalid g1 a \/ a = e;
  addEdge_step_aux: forall x y a,
    step_aux g2 a x y <->
      step_aux g1 a x y \/ (a = e /\ ((x = u /\ y = v) \/ (x = v /\ y = u)));
}.

Class addLeafExist (G V E: Type) {pg: Graph G V E} {gv: GValid G} :=
  addLeaf_valid: forall g u v e, 
    gvalid g ->
    step_aux g e u v -> 
    (forall w, (exists a, step_aux g a w v) -> u = w) ->
    exists h, gvalid h /\ (vvalid h u /\ ~ vvalid h v /\ ~ evalid h e) /\ addEdge h g u v e.


Class addEdgeExist (G V E: Type) {pg: Graph G V E} {gv: GValid G} := {
  addEdge_valid: forall g u v e, 
    gvalid g -> 
    vvalid g u -> vvalid g v -> ~ evalid g e ->
    exists h, gvalid h /\ addEdge g h u v e;
  addEdge_valid_inv: forall g u v e, 
    gvalid g -> 
    vvalid g u -> vvalid g v -> evalid g e ->
    step_aux g e u v ->
    exists h, gvalid h /\ addEdge h g u v e /\ (vvalid h u /\ vvalid h v /\ ~ evalid h e);
}.

Class addEdgeGValid (G V E: Type) {pg: Graph G V E} {gv: GValid G} := {
  addEdge_gvalid: forall g h u v e,
    gvalid g ->
    addEdge g h u v e -> 
    gvalid h;
}. 

Section SUBGRAGH.

Context {G1 G2 V E: Type}
        {graph1: Graph G1 V E}
        {graph2: Graph G2 V E}
        {gvalid1: GValid G1}
        {gvalid2: GValid G2}
        {stepvalid1: StepValid G1 V E}
        {stepvalid2: StepValid G2 V E}
        (g1: G1)
        (g2: G2)
        {g_valid1: gvalid g1}
        {g_valid2: gvalid g2}
        (sub: subgraph g1 g2).

Lemma sub_step': forall x y,
  step g1 x y -> 
  step g2 x y.
Proof.
  intros.
  destruct H as [e ?].
  apply sub in H.
  exists e; auto.
Qed.

Lemma sub_reachable: forall x y, 
  reachable g1 x y -> 
  reachable g2 x y.
Proof.
  intros. 
  unfold reachable in *.
  induction_1n H.
  - reflexivity.
  - transitivity x0; auto.
    apply step_rt. 
    destruct H0 as [e ?].
    apply sub in H0.
    exists e; auto.
Qed.

Lemma sub_reachable_tl(P: V -> Prop): 
  forall x y, 
  reachable_tl P g1 x y -> reachable_tl P g2 x y.
Proof.
  intros.
  unfold reachable_tl in *.
  induction_1n H.
  - reflexivity.
  - transitivity x0; auto.
    apply step_tl_rt; auto.
    destruct H0 as [H0 ?]. 
    split; auto.
    destruct H0 as [e0 H0].
    apply sub in H0.
    exists e0; auto.
Qed.

Lemma sub_reachable_without: forall e x y, 
  reachable_without g1 e x y -> 
  reachable_without g2 e x y.
Proof.
  intros.
  unfold reachable_without in *.
  induction_1n H.
  - reflexivity.
  - transitivity x0; auto.
    apply step_without_rt; auto.
    destruct H0 as [e0 [? ?]].
    exists e0; split; auto.
Qed.

Lemma sub_reverse {no_empty_edge1: NoEmptyEdge G1 V E}
  {step_aux_unique_undirected2: StepUniqueUndirected G2 V E}: 
  forall x y e, 
    step_aux g2 e x y -> 
    evalid g1 e ->
    step_aux g1 e x y \/ step_aux g1 e y x.
Proof.
  intros.
  apply no_empty_edge in H0; auto.
  destruct H0 as [a [b ?]].
  apply sub in H0 as H1.
  eapply step_aux_unique_undirected in H as Heq; eauto.
  destruct Heq as [Heq | Heq]; destruct Heq; subst; tauto.
Qed.

Lemma evalid_sub_vvalid1
  {no_empty_edge1: NoEmptyEdge G1 V E}
  {step_aux_unique_undirected2: StepUniqueUndirected G2 V E}: 
  forall u v e,
    step_aux g2 e u v ->
    evalid g1 e ->
    vvalid g1 v.
Proof.
  intros.
  eapply sub_reverse in H0 as []; eauto;
  [eapply step_vvalid2 | eapply step_vvalid1]; eauto.
Qed.

Lemma evalid_sub_vvalid2
  {no_empty_edge1: NoEmptyEdge G1 V E}
  {step_aux_unique_undirected2: StepUniqueUndirected G2 V E}: 
  forall u v e,
    step_aux g2 e u v ->
    evalid g1 e ->
    vvalid g1 u.
Proof.
  intros.
  eapply sub_reverse in H0 as []; eauto;
  [eapply step_vvalid1 | eapply step_vvalid2]; eauto.
Qed.

Lemma sub_evalid 
  {no_empty_edge: NoEmptyEdge G1 V E}: 
  forall e,
  evalid g1 e ->
  evalid g2 e.
Proof.
  intros.
  apply no_empty_edge in H as [x [y Hstep]]; auto.
  apply sub in Hstep. 
  eapply step_evalid; eauto.
Qed.
    
End SUBGRAGH.

Section ADDLEAF.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context (g1 g2: G)
        {g_valid1: gvalid g1}
        {g_valid2: gvalid g2}.

(* 在该前提下进行的加边操作的基本性质 *)
Context (u v: V)
        (e: E)
        (Hu: vvalid g1 u)
        (Hv: ~ vvalid g1 v)
        (He: ~ evalid g1 e)
        (Hadd: addEdge g1 g2 u v e). 

Lemma addEdge_subgraph: 
  subgraph g1 g2.
Proof.
  unfold subgraph.
  intros. 
  apply Hadd; left; auto.
Qed.

Lemma addEdge_new_step_aux:
  forall x y a,
    step_aux g2 a x y ->
    a <> e ->
    step_aux g1 a x y.
Proof.
  intros x y a Hstep Hneq.
  destruct Hadd as [_ _ Hstep_add].
  apply Hstep_add in Hstep as [Hold | [Heq _]]; auto.
  contradiction.
Qed.

Lemma addEdge_new_step_uv:
  step_aux g2 e u v.
Proof.
  destruct Hadd as [_ _ Hstep_add].
  apply Hstep_add.
  right; split; [reflexivity | left; split; reflexivity].
Qed.

Lemma addEdge_new_step_vu:
  step_aux g2 e v u.
Proof.
  apply step_sym.
  apply addEdge_new_step_uv.
Qed.

Lemma addEdge_new_vertex_is_leaf:
  exists ! x, exists a, step_aux g2 a x v.
Proof.
  exists u.
  split.
  - exists e; apply addEdge_new_step_uv.
  - intros x [a Hstep].
    destruct Hadd as [ _ _ Hstep_add].
    apply Hstep_add in Hstep as [Hold | [Heq [[Hx Hy] | [Hx Hy]]]].
    + exfalso.
      apply Hv.
      eapply step_vvalid2; eauto.
    + subst; reflexivity.
    + subst; auto.
Qed.

Lemma addEdge_vlist_permutation:
  forall (vlist1 vlist2: list V),
    NoDup vlist1 ->
    (forall x, In x vlist1 <-> vvalid g1 x) ->
    NoDup vlist2 ->
    (forall x, In x vlist2 <-> vvalid g2 x) ->
    Permutation vlist2 (v :: vlist1).
Proof.
  intros vlist1 vlist2 Hnodup1 Hviff1 Hnodup2 Hviff2. 
  destruct Hadd as [ _ _ Hstep_add].
  apply NoDup_Permutation; auto.
  - constructor; auto.
    intro Hin.
    apply Hv.
    apply Hviff1; auto.
  - intros x; split; intros Hin.
    + apply Hviff2 in Hin.
      destruct Hadd as [Hadd_vvalid _].
      apply Hadd_vvalid in Hin as [|[|]]; subst; simpl; auto.
      right; apply Hviff1; auto. 
      right; apply Hviff1; auto. 
    + apply Hviff2.
      destruct Hadd as [Hadd_vvalid _].
      apply Hadd_vvalid.
      destruct Hin; [right|left]; auto. 
      apply Hviff1; auto.
Qed.

Lemma addEdge_elist_permutation:
  forall (elist1 elist2: list E),
    NoDup elist1 ->
    (forall a, In a elist1 <-> evalid g1 a) ->
    NoDup elist2 ->
    (forall a, In a elist2 <-> evalid g2 a) ->
    Permutation elist2 (e :: elist1).
Proof.
  intros elist1 elist2 Hnodup1 Heiff1 Hnodup2 Heiff2.
  destruct Hadd as [ _ _ Hstep_add].
  apply NoDup_Permutation; auto.
  - constructor; auto.
    intro Hin.
    apply He.
    apply Heiff1; auto.
  - intros a; split; intros Hin.
    + apply Heiff2 in Hin.
      destruct Hadd as [_ Hadd_evalid].
      apply Hadd_evalid in Hin as [Hin | Hin]; simpl; auto. 
      right; apply Heiff1; auto.
    + apply Heiff2.
      destruct Hadd as [_ Hadd_evalid].
      apply Hadd_evalid.
      destruct Hin; [right|left]; auto. 
      apply Heiff1; auto.
Qed.


Lemma addEdge_valid_epath_old_to_new:
  forall x p y, valid_epath g1 x p y -> valid_epath g2 x p y.
Proof.
  intros x p.
  revert x.
  induction p as [|a p IHp]; intros x y Hpath.
  - apply valid_epath_nil_inv in Hpath; subst.
    apply valid_epath_empty.
  - apply valid_epath_cons_inv in Hpath as [z [Hstep Hrest]].
    eapply valid_epath_cons.
    + apply addEdge_subgraph; exact Hstep.
    + apply IHp; exact Hrest.
Qed.

Lemma addEdge_valid_epath_new_to_old:
  forall x p y,
    valid_epath g2 x p y ->
    ~ In e p ->
    valid_epath g1 x p y.
Proof.
  intros x p.
  revert x.
  induction p as [|a p IHp]; intros x y Hpath Hfor.
  - apply valid_epath_nil_inv in Hpath; subst.
    apply valid_epath_empty.
  - simpl in Hfor.
    apply valid_epath_cons_inv in Hpath as [z [Hstep Hrest]].
    eapply valid_epath_cons.
    + eapply addEdge_new_step_aux; eauto.
    + apply IHp; auto.
Qed.

Lemma addEdge_no_epath_from_new_without_edge:
  forall p x,
    valid_epath g2 v p x ->
    ~ In e p ->
    x = v.
Proof.

  intros p.
  induction p as [|a p IHp]; intros x Hpath Hfor.
  - apply valid_epath_nil_inv in Hpath; auto.
  - simpl in Hfor.
    apply valid_epath_cons_inv in Hpath as [z [Hstep Hrest]].
    destruct Hadd as [ _ _ Hstep_add].
    apply Hstep_add in Hstep as [Hold | [Heq _]].
    + exfalso.
      apply Hv.
      eapply step_vvalid1; eauto.
    + destruct Hfor; subst; left; auto.
Qed.

Lemma addEdge_no_epath_to_new_without_edge:
  forall x p,
    valid_epath g2 x p v ->
    ~ In e p ->
    x = v.
Proof.
  intros x p Hpath Hfor. 
  rewrite in_rev in Hfor.
  pose proof (valid_epath_rev g2 x p v Hpath) as Hrev.
  eapply addEdge_no_epath_from_new_without_edge; eauto.
Qed. 

Lemma addEdge_simple_epath_old_endpoints_not_in_new_edge:
  forall x p y,
    x <> v ->
    y <> v ->
    is_simple_epath g2 x p y ->
    ~ In e p.
Proof.
  intros x p y Hxv Hyv [Hpath Hnodup] Hin.
  apply in_split in Hin as [l1 [l2 Hp]].
  subst p.
  apply valid_epath_app_inv in Hpath as [a [Hl1 Hrest]].
  apply valid_epath_cons_inv in Hrest as [b [Hstep Hl2]]. 
  apply NoDup_remove_2 in Hnodup. 
  rewrite in_app_iff in Hnodup.
  pose proof Hadd as Hadd'.
  destruct Hadd' as [ _ _ Hstep_add].
  apply Hstep_add in Hstep as [Hold | [Heq [[Ha Hb] | [Ha Hb]]]]; subst.
  * apply He.
    eapply step_evalid; eauto.
  * assert (y = v) by (eapply addEdge_no_epath_from_new_without_edge; eauto).
    contradiction.
  * assert (x = v) by (eapply addEdge_no_epath_to_new_without_edge; eauto).
    contradiction.
Qed.

Lemma addEdge_simple_cycle_not_in_new_edge:
  forall x p,
    is_simple_epath g2 x p x ->
    ~ In e p.
Proof.
  intros x p [Hpath Hnodup] Hin.
  apply in_split in Hin as [l1 [l2 Hp]]; subst.
  apply valid_epath_app_inv in Hpath as [a [Hl1 Hrest]].
  apply valid_epath_cons_inv in Hrest as [b [Hstep Hl2]].
  apply NoDup_remove_2 in Hnodup. 
  rewrite in_app_iff in Hnodup.
  pose proof Hadd as Hadd'.
  destruct Hadd' as [ _ _ Hstep_add].
  apply Hstep_add in Hstep as [Hold | [Heq [[Ha Hb] | [Ha Hb]]]]; subst.
  * apply He; eapply step_evalid; eauto.
  * assert (x = v) by (eapply addEdge_no_epath_from_new_without_edge; eauto); subst.
    assert (u = v) by (eapply addEdge_no_epath_from_new_without_edge; eauto); subst. 
    auto.
  * assert (x = v) by (eapply addEdge_no_epath_to_new_without_edge; eauto); subst.
    assert (u = v) by (eapply addEdge_no_epath_to_new_without_edge; eauto); subst.
    auto.
Qed.

End ADDLEAF.

Section ADDNEWEDGE. 

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {finitegraph: FiniteGraph G V E}
        {simplegraph: SimpleGraph G V E}
        {addLeafExist: addLeafExist G V E}. (*要求原图的加边存在性*)

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context (g1 g2: G)
        {g_valid1: gvalid g1}
        {g_valid2: gvalid g2}.

Context (u v: V)
        (e: E)
        (Hu: vvalid g1 u)
        (Hv: vvalid g1 v)
        (He: ~ evalid g1 e)
        (Hadd: addEdge g1 g2 u v e). 

#[export]Instance vlist_bijective: VListBijective G V E.
Proof. apply finite_graph_vlist_bijective; auto. Qed.

#[export]Instance elist_bijective: EListBijective G V E.
Proof. 
  apply finite_egraph_elist_bijective; auto.
  apply finite_graph_finite_egraph; auto. 
Qed.

Lemma addEdge2_vvalid_iff:
  forall x,
    vvalid g2 x <-> vvalid g1 x.
Proof.
  intros x.
  destruct Hadd as [Hvvalid _ Hstep_add].
  rewrite Hvvalid.
  split; subst; auto. 
  intros [|[|]]; subst; auto. 
Qed.

Lemma addEdge2_evalid_iff:
  forall a,
    evalid g2 a <-> evalid g1 a \/ a = e.
Proof.
  intros a.
  destruct Hadd as [_ Hevalid _].
  apply Hevalid.
Qed.

Lemma addEdge2_old_step:
  forall x y a,
    step_aux g1 a x y ->
    step_aux g2 a x y.
Proof.
  intros x y a Hstep.
  destruct Hadd as [_ _ Hstep_add].
  apply Hstep_add; left; auto.
Qed.

Lemma addEdge2_new_step_uv: 
  step_aux g2 e u v.
Proof.
  destruct Hadd as [_ _ Hstep_add].
  apply Hstep_add; right; split; [reflexivity | left; split; reflexivity].
Qed.

Lemma addEdge2_new_step_vu:
  step_aux g2 e v u.
Proof.
  destruct Hadd as [_ _ Hstep_add].
  apply Hstep_add; right; split; [reflexivity | right; split; reflexivity].
Qed.

Lemma addEdge2_keep_step:
  forall x y a,
    step_aux g2 a x y ->
    a <> e ->
    step_aux g1 a x y.
Proof.
  intros x y a Hstep Hneq.
  destruct Hadd as [_ _ Hstep_add].
  apply Hstep_add in Hstep as [Hold | [Heq _]]; auto.
  contradiction.
Qed.

Lemma addEdge2_vlist_permutation:
  Permutation (bijective_listV g2) (bijective_listV g1).
Proof.
  apply NoDup_Permutation.
  - apply bijective_listV_NoDup; auto.
  - apply bijective_listV_NoDup; auto.
  - intros x.
    rewrite !bijective_vertices; auto.
    apply addEdge2_vvalid_iff; auto.
Qed.

Lemma addEdge2_elist_permutation:
  Permutation (bijective_listE g2) (e :: bijective_listE g1).
Proof.
  destruct Hadd as [Hvvalid Hevalid Hstep_aux].
  apply NoDup_Permutation.
  - apply bijective_listE_NoDup; auto.
  - constructor.
    + intro Hin.
      apply He.
      apply bijective_edges; auto.
    + apply bijective_listE_NoDup; auto.
  - intros a; split; intros Hin.
    + apply bijective_edges in Hin; auto.
      apply Hevalid in Hin as [Hin | Hin].
      * right; apply bijective_edges; auto.
      * subst; left; auto.
    + apply bijective_edges; auto.
      simpl in Hin.
      apply Hevalid.
      destruct Hin as [Hin | Hin]; [right | left]; auto.
      apply bijective_edges; auto.
Qed.

Lemma addEdge2_valid_epath: 
  forall p x y, 
    valid_epath g1 x p y ->
    valid_epath g2 x p y.
Proof. 
  induction p as [|a p IHp]; intros.
  - apply valid_epath_nil_inv in H; subst.
    apply valid_epath_empty.
  - apply valid_epath_cons_inv in H as [z [Hstep Hrest]].
    eapply valid_epath_cons with (v:=z); eauto.
    destruct Hadd as [ _ _ Hstep_aux]. 
    apply Hstep_aux; left; auto. 
Qed.


Lemma addEdge2_valid_epath_new_to_old:
  forall p x y,
    valid_epath g2 x p y ->
    ~ In e p ->
    valid_epath g1 x p y.
Proof.
  intros p.
  induction p as [|a p IHp]; intros x y Hpath Hnotin.
  - apply valid_epath_nil_inv in Hpath; subst.
    apply valid_epath_empty.
  - simpl in Hnotin.
    apply valid_epath_cons_inv in Hpath as [z [Hstep Hrest]].
    eapply valid_epath_cons with (v:=z).
    + eapply addEdge2_keep_step; eauto.
    + eapply IHp; eauto.
Qed.

Lemma addEdge2_edge_not_in_old_path:
  forall p x y,
    valid_epath g1 x p y ->
    ~ In e p.
Proof.
  intros p.
  induction p as [|a p IHp]; intros x y Hpath Hin; simpl in Hin; [contradiction|].
  apply valid_epath_cons_inv in Hpath as [z [Hstep Hrest]].
  destruct Hin as [Hin | Hin].
  - subst a. apply He. eapply step_evalid; eauto.
  - eapply IHp; eauto.
Qed.

Lemma addEdge2_cycle_without_new_edge_simple:
  forall z p,
    is_simple_epath g2 z p z ->
    In e p ->
    exists q,
      is_simple_epath g1 u q v /\
      (forall a, In a q <-> In a p /\ a <> e).
Proof.
  intros z p [Hpath Hnodup] Hin.
  apply in_split in Hin as [p1 [p2 Hp]].
  subst p. 
  assert (Hstep: step_aux g2 e u v) by (apply addEdge2_new_step_uv; auto).
  apply valid_epath_app_inv in Hpath as [s [Hpre Hrest]].
  apply valid_epath_cons_inv in Hrest as [t [Hstep_e Hpost]].
  eapply step_aux_unique_undirected in Hstep_e as [[]|[]]; eauto; subst s t.
  - exists (rev (p2 ++ p1)); split; [split|].
    + apply valid_epath_rev.
      eapply addEdge2_valid_epath_new_to_old; eauto; 
      [eapply valid_epath_app; eauto|].
      intros Hin; rewrite in_app_iff in Hin.
      destruct (Nodup_split_constructors _ _ _ Hnodup); tauto.
    + apply NoDup_rev.
      apply Nodup_app_comm. 
      eapply NoDup_remove_1; eauto.
    + intros a.
      rewrite <- in_rev, in_app_iff.
      split; [intros [|]; split|intros].
      * rewrite in_app_iff; right; simpl; right; auto.
      * intro Heq; subst.
        destruct (Nodup_split_constructors _ _ _ Hnodup); contradiction.
      * rewrite in_app_iff; left; auto.
      * intro Heq; subst.
        destruct (Nodup_split_constructors _ _ _ Hnodup); contradiction.
      * rewrite in_app_iff in H.
        destruct H as [[|[|]]]; subst; try tauto.
  - exists (p2 ++ p1); split; [split|].
    + eapply addEdge2_valid_epath_new_to_old; eauto; 
      [eapply valid_epath_app; eauto|].
      intros Hin; rewrite in_app_iff in Hin.
      destruct (Nodup_split_constructors _ _ _ Hnodup); tauto.
    + apply Nodup_app_comm.
      eapply NoDup_remove_1; eauto.
    + intros a.
      rewrite in_app_iff; split; [intros [|]; split|intros].
      * rewrite in_app_iff; right; simpl; right; auto.
      * intro Heq; subst.
        destruct (Nodup_split_constructors _ _ _ Hnodup); contradiction.
      * rewrite in_app_iff; left; auto.
      * intro Heq; subst.
        destruct (Nodup_split_constructors _ _ _ Hnodup); contradiction.
      * rewrite in_app_iff in H.
        destruct H as [[|[|]]]; subst; try tauto.
Qed.

End ADDNEWEDGE.
