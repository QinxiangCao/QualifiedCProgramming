Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Section graph_basic.

Class Graph (G V E: Type) := {
  vvalid : G -> V -> Prop;
  evalid : G -> E -> Prop;
  step_aux : G -> E -> V -> V -> Prop;
}.

Class GValid (G: Type) :=
  gvalid : G -> Prop.

Class StepValid (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  step_vvalid1: forall g e x y, step_aux g e x y -> vvalid g x ;
  step_vvalid2: forall g e x y, step_aux g e x y -> vvalid g y ;
  step_evalid: forall g e x y, step_aux g e x y -> evalid g e ;
}.

Class NoEmptyEdge (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  no_empty_edge: forall g e, gvalid g -> evalid g e -> exists x y, step_aux g e x y ;
}.

Class UndirectedGraph (G V E: Type) `{pg: Graph G V E} `{gv: GValid G}:= {
  step_sym: forall g e x y, step_aux g e x y -> step_aux g e y x;
}.

Class StepUniqueDirected (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  step_aux_unique: forall g e x1 y1 x2 y2, gvalid g -> step_aux g e x1 y1 -> step_aux g e x2 y2 -> 
  x1 = x2 /\ y1 = y2;
}.

Class StepUniqueUndirected (G V E: Type) `{pg: Graph G V E} `{gv: GValid G}:= {
  step_aux_unique_undirected: forall g e x1 y1 x2 y2, gvalid g -> step_aux g e x1 y1 -> step_aux g e x2 y2 -> 
  (x1 = x2 /\ y1 = y2) \/ (x1 = y2 /\ x2 = y1);
}.

Class SimpleGraph (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  no_multiple_edge: forall g e1 e2 x y, gvalid g -> step_aux g e1 x y -> step_aux g e2 x y -> e1 = e2;
  no_self_loop: forall g e x, gvalid g -> ~ step_aux g e x x;
}.

Class FiniteGraph (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  listV: G -> list V;
  finite_vertices: forall g, gvalid g -> forall v, vvalid g v -> In v (listV g);
}.

Fixpoint valid_NoDup_list {A: Type} (P: A -> Prop) (l: list A): list A :=
  match l with
  | nil => nil
  | x :: xs =>
      let ys := valid_NoDup_list P xs in
      if excluded_middle_informative (P x /\ ~ In x ys)
      then x :: ys
      else ys
  end.

Lemma valid_NoDup_list_NoDup:
  forall {A: Type} (P: A -> Prop) (l: list A),
    NoDup (valid_NoDup_list P l).
Proof.
  intros A P l.
  induction l as [|x xs IH]; simpl; [constructor|].
  destruct (excluded_middle_informative (P x /\ ~ In x (valid_NoDup_list P xs))) as [[_ Hnotin]|_].
  - constructor; auto.
  - auto.
Qed.

Lemma valid_NoDup_list_spec:
  forall {A: Type} (P: A -> Prop) (l: list A) x,
    In x (valid_NoDup_list P l) <-> In x l /\ P x.
Proof.
  intros A P l.
  induction l as [|a xs IH]; intros x; simpl; 
  [split; tauto|].
  destruct (excluded_middle_informative (P a /\ ~ In a (valid_NoDup_list P xs))) as [[Ha Hnotin]|Hbad].
  + simpl; split.
    * intros [Hx|Hin].
      - subst. split; [left; reflexivity|auto].
      - apply IH in Hin as [Hin HPx]. split; [right; auto|auto].
    * intros [[Hx|Hin] HPx].
      - subst. left; reflexivity.
      - right. apply IH. split; auto.
  + split.
    * intros Hin. apply IH in Hin as [Hin HPx]. split; [right; auto|auto].
    * intros [[Hx|Hin] HPx].
      - subst.
        destruct (classic (In x (valid_NoDup_list P xs))) as [Hin_clean|Hnotin_clean]; auto.
        exfalso. apply Hbad. split; auto.
      - apply IH. split; auto.
Qed.

Class VListBijective (G V E: Type) {pg: Graph G V E} {gv: GValid G} := {
  bijective_listV: G -> list V;
  bijective_listV_NoDup: forall g, gvalid g -> NoDup (bijective_listV g);
  bijective_vertices: forall g, gvalid g -> forall v, In v (bijective_listV g) <-> vvalid g v;
}.

Definition cleaned_listV
  {G V E: Type} {pg: Graph G V E} {gv: GValid G}
  {fg: FiniteGraph G V E}
  (g: G): list V :=
  valid_NoDup_list (vvalid g) (listV g).

Lemma finite_graph_vlist_bijective
  (G V E: Type) {pg: Graph G V E} {gv: GValid G}
  {fg: FiniteGraph G V E}:
  VListBijective G V E.
Proof.
  refine {| bijective_listV := cleaned_listV |}.
  - intros g Hg. unfold cleaned_listV. apply valid_NoDup_list_NoDup.
  - intros g Hg v. unfold cleaned_listV.
    rewrite valid_NoDup_list_spec.
    split.
    + intros [_ Hvalid]; auto.
    + intros Hvalid. split; auto.
      apply finite_vertices; auto.
Qed.

Class FiniteEGraph (G V E: Type) {pg: Graph G V E} {gv: GValid G} := {
  listE: G -> list E;
  finite_edges: forall g, gvalid g -> forall e, evalid g e -> In e (listE g);
}.



Class EListBijective (G V E: Type) {pg: Graph G V E} {gv: GValid G} := {
  bijective_listE: G -> list E;
  bijective_listE_NoDup: forall g, gvalid g -> NoDup (bijective_listE g);
  bijective_edges: forall g, gvalid g -> forall e, In e (bijective_listE g) <-> evalid g e;
}.

Definition cleaned_listE
  {G V E: Type} {pg: Graph G V E} {gv: GValid G}
  {fg: FiniteEGraph G V E}
  (g: G): list E :=
  valid_NoDup_list (evalid g) (listE g).

Lemma finite_egraph_elist_bijective
  (G V E: Type) {pg: Graph G V E} {gv: GValid G}
  {fg: FiniteEGraph G V E}:
  EListBijective G V E.
Proof.
  refine {| bijective_listE := cleaned_listE |}.
  - intros g Hg. unfold cleaned_listE. apply valid_NoDup_list_NoDup.
  - intros g Hg e. unfold cleaned_listE.
    rewrite valid_NoDup_list_spec.
    split.
    + intros [_ Hevalid]; auto.
    + intros Hevalid. split; auto.
      apply finite_edges; auto.
Qed.

Definition edge_between_list
  {G V E: Type} {pg: Graph G V E}
  (g: G) (x y: V): list E :=
  match excluded_middle_informative (exists e, step_aux g e x y) with
  | left Hex =>
      proj1_sig (@constructive_indefinite_description E (fun e => step_aux g e x y) Hex) :: nil
  | right _ => nil
  end.

Definition raw_listE_from_vlist
  {G V E: Type} {pg: Graph G V E}
  (g: G) (vl: list V): list E :=
  flat_map (fun x => flat_map (fun y => edge_between_list g x y) vl) vl.

Lemma edge_between_list_intro:
  forall {G V E: Type} {pg: Graph G V E} {gv: GValid G} {sg: SimpleGraph G V E} 
  (g: G) (x y: V) (e: E),
    gvalid g ->
    step_aux g e x y ->
    In e (edge_between_list g x y).
Proof.
  intros G V E pg gv sg g x y e Hg Hstep.
  unfold edge_between_list.
  destruct (excluded_middle_informative (exists e0 : E, step_aux g e0 x y)) as [Hex|Hnone].
  - destruct (@constructive_indefinite_description E (fun e0 => step_aux g e0 x y) Hex) as [a Ha].
    simpl. left. eapply no_multiple_edge; eauto.
  - exfalso. apply Hnone. exists e; auto.
Qed.

Lemma raw_listE_from_vlist_intro:
  forall {G V E: Type} {pg: Graph G V E} {gv: GValid G}
         {sg: SimpleGraph G V E} (g: G) vl x y e,
    gvalid g ->
    In x vl ->
    In y vl ->
    step_aux g e x y ->
    In e (raw_listE_from_vlist g vl).
Proof.
  intros G V E pg gv sg g vl x y e Hg Hx Hy Hstep.
  unfold raw_listE_from_vlist.
  apply in_flat_map.
  exists x. split; auto.
  apply in_flat_map.
  exists y. split; auto.
  eapply edge_between_list_intro; eauto.
Qed.

Definition listE_from_finite_graph
  {G V E: Type} {pg: Graph G V E} {gv: GValid G}
  {fg: FiniteGraph G V E}
  (g: G): list E :=
  raw_listE_from_vlist g (listV g).

Lemma finite_graph_finite_egraph
  (G V E: Type) {pg: Graph G V E} {gv: GValid G}
  {stepvalid: StepValid G V E}
  {noemptyedge: NoEmptyEdge G V E}
  {sg: SimpleGraph G V E}
  {fg: FiniteGraph G V E}:
  FiniteEGraph G V E.
Proof.
  refine {| listE := listE_from_finite_graph |}.
  intros g Hg e He.
  eapply no_empty_edge in He as [x [y Hstep]]; eauto.
  unfold listE_from_finite_graph.
  eapply raw_listE_from_vlist_intro; eauto.
  - apply finite_vertices; [auto|eapply step_vvalid1; eauto].
  - apply finite_vertices; [auto|eapply step_vvalid2; eauto].
Qed.

Definition vertex_num 
  {G V E: Type} {pg: Graph G V E} {gv: GValid G} 
  {vb: VListBijective G V E} (g: G):= Zlength (bijective_listV g).

Definition edge_num 
  {G V E: Type} {pg: Graph G V E} {gv: GValid G} 
  {eb: EListBijective G V E} (g: G):= Zlength (bijective_listE g).

End graph_basic.

