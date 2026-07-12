(* Concrete Path instance for GraphLib on a GRID graph whose vertices are
   CELLS (Z*Z).  This is a verbatim port of GraphInstances.v (an integer-vertex
   graph) to vertex type (Z*Z): the only change is the vertex type and the
   default vertex element (0,0) wherever GraphInstances used 0. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import ListLib.Base.Positional.
From GraphLib Require Import graph_basic reachable_basic.
From GraphLib Require Import path vpath path_basic.

Import ListNotations.
Local Open Scope Z_scope.

(* ============================================================ *)
(*  Concrete grid graph.                                         *)
(*  Vertices: Z*Z (a cell). Edges: (Z*Z)*(Z*Z).                  *)
(* ============================================================ *)

Record GridGraph := {
  gv : (Z*Z) -> Prop;            (* vertex membership *)
  ge : (Z*Z) -> (Z*Z) -> Prop;   (* adjacency relation *)
}.

(* GRAPH-AWARE step relation. *)
Definition gstep_aux (g: GridGraph) (xy: (Z*Z)*(Z*Z)) (x y: Z*Z): Prop :=
  x = fst xy /\ y = snd xy /\ ge g x y /\ gv g x /\ gv g y.

Definition gevalid (g: GridGraph) (xy: (Z*Z)*(Z*Z)): Prop :=
  ge g (fst xy) (snd xy) /\ gv g (fst xy) /\ gv g (snd xy).

#[export] Instance GridGraph_graph : Graph GridGraph (Z*Z) ((Z*Z)*(Z*Z)) := {|
  vvalid := gv;
  evalid := gevalid;
  step_aux := gstep_aux;
|}.

#[export] Instance GridGraph_gvalid : GValid GridGraph :=
  fun _ => True.

#[export] Instance GridGraph_stepvalid : StepValid GridGraph (Z*Z) ((Z*Z)*(Z*Z)).
Proof.
  constructor.
  - (* step_vvalid1 *)
    intros g e x y Hstep. simpl in Hstep.
    unfold gstep_aux in Hstep. tauto.
  - (* step_vvalid2 *)
    intros g e x y Hstep. simpl in Hstep.
    unfold gstep_aux in Hstep. tauto.
  - (* step_evalid *)
    intros g e x y Hstep. simpl in Hstep.
    unfold gstep_aux in Hstep. destruct Hstep as [Hx [Hy [He [Hvx Hvy]]]].
    simpl. unfold gevalid. subst. auto.
Defined.

(* ============================================================ *)
(*  Concrete path type: a vertex list bundled with an edge list. *)
(* ============================================================ *)

Record GPath := mkGPath {
  gpv : list (Z*Z);
  gpe : list ((Z*Z)*(Z*Z));
}.

(* Helper list lemmas about hd/last vs hd_error/tl_error. *)
Lemma hd_error_hd {A: Type} (d: A) (l: list A):
  l <> nil -> hd_error l = Some (hd d l).
Proof. destruct l; [congruence|]. reflexivity. Qed.

Lemma tl_error_last {A: Type} (d: A) (l: list A):
  l <> nil -> tl_error l = Some (last l d).
Proof.
  intros Hnn.
  pose proof (app_removelast_last d Hnn) as Heq.
  transitivity (tl_error (removelast l ++ [last l d])).
  { f_equal. exact Heq. }
  rewrite Positional.tl_error_last. reflexivity.
Qed.

Definition gpath_valid (g: GridGraph) (p: GPath): Prop :=
  gpv p <> nil /\ vpath_iff_epath_prop g (gpv p) (gpe p).

#[export] Instance GridGraph_path : Path GridGraph (Z*Z) ((Z*Z)*(Z*Z)) GPath.
Proof.
  refine {|
    path_valid := gpath_valid;
    vertex_in_path := gpv;
    head := fun p => hd (0,0) (gpv p);
    tail := fun p => last (gpv p) (0,0);
    edge_in_path := gpe;
  |}.
  - (* head_valid *)
    intros g p [Hnn _]. symmetry. apply hd_error_hd; auto.
  - (* tail_valid *)
    intros g p [Hnn _]. symmetry. apply tl_error_last; auto.
  - (* vpath_iff_epath *)
    intros g p [_ Hcoh]. exact Hcoh.
Defined.

(* ============================================================ *)
(*  EmptyPath: single vertex, no edges.                         *)
(* ============================================================ *)

#[export] Instance GridGraph_emptypath : EmptyPath GridGraph (Z*Z) ((Z*Z)*(Z*Z)) GPath GridGraph_path.
Proof.
  refine {| empty_path := fun v => mkGPath [v] [] |}.
  - (* empty_path_valid *)
    intros g v. split.
    + discriminate.
    + constructor.
      * reflexivity.
      * intros n u v0 e Hn _ _ _. simpl in Hn. lia.
  - (* empty_path_vertex *)
    reflexivity.
Defined.

(* ============================================================ *)
(*  SinglePath: two vertices, one edge.                         *)
(* ============================================================ *)

#[export] Instance GridGraph_singlepath : SinglePath GridGraph (Z*Z) ((Z*Z)*(Z*Z)) GPath GridGraph_path.
Proof.
  refine {| single_path := fun u v e => mkGPath [u; v] [e] |}.
  - (* single_path_valid *)
    intros g u v e Hstep. split.
    + discriminate.
    + constructor.
      * reflexivity.
      * intros n u0 v0 e0 Hn He Hu Hv. simpl in Hn.
        assert (n = 0%nat) by lia. subst n.
        simpl in He, Hu, Hv.
        inversion He; inversion Hu; inversion Hv; subst.
        exact Hstep.
  - (* single_path_vertex *)
    reflexivity.
  - (* single_path_edge *)
    reflexivity.
Defined.

(* ============================================================ *)
(*  ConcatPath: append vertices (dropping head of second) and    *)
(*  edges.                                                        *)
(* ============================================================ *)

Definition gconcat (a1 a2: GPath): GPath :=
  mkGPath (gpv a1 ++ tl (gpv a2)) (gpe a1 ++ gpe a2).

(* nth_error of an append where index lands in the first part. *)
Lemma nth_error_app_l {A: Type} (l1 l2: list A) (n: nat):
  (n < length l1)%nat -> nth_error (l1 ++ l2) n = nth_error l1 n.
Proof.
  revert n. induction l1 as [|x xs IH]; intros n Hn; simpl in *.
  - lia.
  - destruct n as [|n']; simpl; auto. apply IH. lia.
Qed.

#[export] Instance GridGraph_concatpath : ConcatPath GridGraph (Z*Z) ((Z*Z)*(Z*Z)) GPath GridGraph_path.
Proof.
  refine {| concat_path := gconcat |}.
  - (* concat_path_valid *)
    intros g a1 a2 [Hnn1 Hcoh1] [Hnn2 Hcoh2] Htail.
    destruct Hcoh1 as [Hlen1 Hstep1].
    destruct Hcoh2 as [Hlen2 Hstep2].
    (* tail a1 = head a2 : last (gpv a1) (0,0) = hd (0,0) (gpv a2) *)
    simpl in Htail.
    split.
    + (* non-empty *)
      unfold gconcat. simpl.
      destruct (gpv a1); [congruence|]. discriminate.
    + unfold gconcat. constructor.
      * (* length *)
        simpl. rewrite !length_app.
        (* length (tl pv2) = length pv2 - 1, and pv2 nonempty *)
        destruct (gpv a2) as [|y2 ys2] eqn:Hv2; [congruence|].
        simpl in Hlen2 |- *. rewrite Hlen1. lia.
      * (* step coherence *)
        intros n u v e Hn He Hu Hv.
        simpl (length _) in Hn. simpl (gpe _) in *. simpl (gpv _) in Hu, Hv.
        rewrite length_app in Hn.
        (* split on whether edge index n is in first edge list *)
        destruct (Nat.ltb_spec n (length (gpe a1))) as [Hlt | Hge].
        -- (* in first part: indices into pv1 region *)
           rewrite nth_error_app_l in He by auto.
           (* vertex indices n and S n are both < length pv1 *)
           assert (Hn_v: (n < length (gpv a1))%nat) by lia.
           assert (HSn_v: (S n < length (gpv a1))%nat) by lia.
           rewrite nth_error_app_l in Hu by auto.
           rewrite nth_error_app_l in Hv by auto.
           apply (Hstep1 n u v e); auto. lia.
        -- (* in second part *)
           rewrite nth_error_app2 in He by auto.
           set (m := (n - length (gpe a1))%nat) in *.
           assert (Hm: (m < length (gpe a2))%nat) by (unfold m; lia).
           (* relate vertex positions in (pv1 ++ tl pv2) to those of pv2 *)
           destruct (gpv a2) as [|y2 ys2] eqn:Hv2; [congruence|].
           simpl (tl _) in Hu, Hv.
           set (L1 := length (gpv a1)) in *.
           assert (HL1: L1 = S (length (gpe a1))) by (unfold L1; lia).
           assert (Hn_eq: n = (L1 - 1 + m)%nat) by (unfold m; lia).
           (* The S n vertex lands in ys2 cleanly. *)
           assert (HvSn: nth_error (gpv a2) (S m) = Some v).
           { rewrite nth_error_app2 in Hv by (unfold L1 in *; lia).
             rewrite Hv2. simpl.
             replace (S n - length (gpv a1))%nat with m in Hv
               by (unfold L1 in *; lia). exact Hv. }
           (* The n-th vertex: either last of pv1 (m=0) or inside ys2. *)
           assert (Hvn: nth_error (gpv a2) m = Some u).
           { destruct m as [|m'] eqn:Hmeq.
             - (* m = 0: index n = L1-1, the last vertex of pv1 *)
               assert (HnL1: n = (L1 - 1)%nat) by lia.
               rewrite nth_error_app_l in Hu by (unfold L1 in *; lia).
               (* nth_error pv1 (L1-1) = tl_error pv1 = Some (last pv1 (0,0)) *)
               assert (Htl1: tl_error (gpv a1) = Some u).
               { unfold tl_error. replace (length (gpv a1) - 1)%nat
                   with n by (unfold L1 in HnL1; lia). exact Hu. }
               rewrite (tl_error_last (0,0)) in Htl1 by auto.
               (* last pv1 (0,0) = tail a1 = head a2 = y2 *)
               inversion Htl1 as [Hlast].
               rewrite Htail in Hlast. simpl in Hlast.
               rewrite Hv2. simpl. congruence.
             - (* m >= 1: index n lands in ys2 *)
               assert (Hnge: (n >= L1)%nat) by lia.
               rewrite nth_error_app2 in Hu by (unfold L1 in *; lia).
               rewrite Hv2. simpl.
               replace (n - length (gpv a1))%nat with m' in Hu
                 by (unfold L1 in *; lia). exact Hu. }
           (* Apply a2's step coherence at edge index m. *)
           rewrite Hv2 in Hvn, HvSn.
           apply (Hstep2 m u v e).
           ++ lia.
           ++ exact He.
           ++ exact Hvn.
           ++ exact HvSn.
  - (* concat_path_vertex *)
    reflexivity.
  - (* concat_path_edge *)
    reflexivity.
Defined.

(* ============================================================ *)
(*  Destruct1nPath: cons-style decomposition of a valid path.    *)
(* ============================================================ *)

Definition gdestruct_1n (g: GridGraph) (p: GPath)
  (H: gpath_valid g p) : @PathConsView GPath ((Z*Z)*(Z*Z)) (Z*Z) :=
  match gpe p with
  | [] => DestructBase1n (hd (0,0) (gpv p))
  | e :: es =>
      DestructStep1n (mkGPath (tl (gpv p)) es)
                     (hd (0,0) (gpv p)) (hd (0,0) (tl (gpv p))) e
  end.

#[export] Instance GridGraph_destruct1npath :
  Destruct1nPath GridGraph (Z*Z) ((Z*Z)*(Z*Z)) GPath GridGraph_path
    GridGraph_emptypath GridGraph_singlepath GridGraph_concatpath.
Proof.
  refine {| destruct_1n_path := gdestruct_1n |}.
  intros g p Hvalid.
  unfold path_cons_spec, gdestruct_1n.
  destruct Hvalid as [Hnn Hcoh].
  destruct Hcoh as [Hlen Hstep].
  destruct p as [pv pe]. simpl in *.
  destruct pe as [|e es]; simpl in *.
  - (* base: pe = [], so pv has length 1 *)
    destruct pv as [|v0 vs]; [congruence|].
    simpl in Hlen.
    assert (vs = []) by (destruct vs; simpl in Hlen; [reflexivity|lia]).
    subst vs. simpl.
    (* empty_path v0 = mkGPath [v0] [] *)
    reflexivity.
  - (* step: pe = e :: es, pv = u :: v1 :: vs *)
    destruct pv as [|u tlpv]; [congruence|].
    destruct tlpv as [|v1 vs]; simpl in Hlen; [lia|].
    simpl.
    split; [|split; [|split]].
    + (* path_valid g (mkGPath (v1::vs) es) *)
      split; [discriminate|].
      constructor.
      * simpl. simpl in Hlen. lia.
      * intros n u0 v0 e0 Hn He0 Hu0 Hv0.
        simpl in Hn, He0, Hu0, Hv0.
        (* shift index by one into the original coherence *)
        apply (Hstep (S n) u0 v0 e0).
        -- simpl. lia.
        -- simpl. exact He0.
        -- simpl. exact Hu0.
        -- simpl. exact Hv0.
    + (* head (mkGPath (v1::vs) es) = v1 *)
      reflexivity.
    + (* step_aux g e u v1 *)
      apply (Hstep 0%nat u v1 e).
      * simpl. lia.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + (* mkGPath (u::v1::vs) (e::es)
           = concat_path (single_path u v1 e) (mkGPath (v1::vs) es) *)
      reflexivity.
Qed.


(* ============================================================ *)
(*  DEMO: the GraphLib predicates are now usable on GridGraph.   *)
(* ============================================================ *)

Definition demo_vpath (g : GridGraph) (u v : Z*Z) (l : list (Z*Z)) : Prop :=
  valid_vpath g u l v.

Definition demo_reach (g : GridGraph) (u v : Z*Z) : Prop :=
  reachable g u v.

Definition demo_simple (g : GridGraph) (p : GPath) (u v : Z*Z) : Prop :=
  is_simple_path g p u v.

(* Sanity: the empty single-vertex path is a valid vpath from v to v. *)
Example demo_vpath_empty (g : GridGraph) (v : Z*Z) : demo_vpath g v v [v].
Proof. unfold demo_vpath. apply valid_vpath_empty. Qed.
