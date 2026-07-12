(* First concrete Path instance for GraphLib on an integer-vertex graph. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import ListLib.Base.Positional.
From GraphLib Require Import graph_basic reachable_basic.
From GraphLib Require Import path vpath path_basic.

Import ListNotations.
Local Open Scope Z_scope.

(* ============================================================ *)
(*  Concrete integer-vertex graph.                              *)
(*  Vertices: Z. Edges: Z*Z (the ordered pair it connects).    *)
(* ============================================================ *)

Record ZGraph := {
  zv : Z -> Prop;       (* vertex membership *)
  ze : Z -> Z -> Prop;  (* adjacency relation *)
}.

(* GRAPH-AWARE step relation.
   Now that the Path class field [vpath_iff_epath_step] takes the graph [g]
   as a parameter (no more universal [forall g]), [step_aux] can depend on
   the graph.  An edge (a,b) is a real step a -> b only when the pair really
   is an edge of [g] AND both endpoints are vertices of [g].  This makes
   [valid_vpath] actually enforce that consecutive vertices are adjacent. *)
Definition zstep_aux (g: ZGraph) (xy: Z*Z) (x y: Z): Prop :=
  x = fst xy /\ y = snd xy /\ ze g x y /\ zv g x /\ zv g y.

Definition zevalid (g: ZGraph) (xy: Z*Z): Prop :=
  ze g (fst xy) (snd xy) /\ zv g (fst xy) /\ zv g (snd xy).

#[export] Instance ZGraph_graph : Graph ZGraph Z (Z*Z) := {|
  vvalid := zv;
  evalid := zevalid;
  step_aux := zstep_aux;
|}.

#[export] Instance ZGraph_gvalid : GValid ZGraph :=
  fun _ => True.

(* With a graph-aware step_aux, StepValid is now provable: step_aux carries
   [zv g x], [zv g y] and [ze g x y] directly. *)
#[export] Instance ZGraph_stepvalid : StepValid ZGraph Z (Z*Z).
Proof.
  constructor.
  - (* step_vvalid1 *)
    intros g e x y Hstep. simpl in Hstep.
    unfold zstep_aux in Hstep. tauto.
  - (* step_vvalid2 *)
    intros g e x y Hstep. simpl in Hstep.
    unfold zstep_aux in Hstep. tauto.
  - (* step_evalid *)
    intros g e x y Hstep. simpl in Hstep.
    unfold zstep_aux in Hstep. destruct Hstep as [Hx [Hy [He [Hvx Hvy]]]].
    simpl. unfold zevalid. subst. auto.
Defined.

(* ============================================================ *)
(*  Concrete path type: a vertex list bundled with an edge list. *)
(* ============================================================ *)

Record ZPath := mkZPath {
  zpv : list Z;
  zpe : list (Z*Z);
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

(* Path interface. head/tail use defaults; path_valid carries the
   real invariant (non-empty vertex list + step coherence). The
   record now takes the graph [g] as a parameter. *)
Definition zpath_valid (g: ZGraph) (p: ZPath): Prop :=
  zpv p <> nil /\ vpath_iff_epath_prop g (zpv p) (zpe p).

#[export] Instance ZGraph_path : Path ZGraph Z (Z*Z) ZPath.
Proof.
  refine {|
    path_valid := zpath_valid;
    vertex_in_path := zpv;
    head := fun p => hd 0 (zpv p);
    tail := fun p => last (zpv p) 0;
    edge_in_path := zpe;
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

#[export] Instance ZGraph_emptypath : EmptyPath ZGraph Z (Z*Z) ZPath ZGraph_path.
Proof.
  refine {| empty_path := fun v => mkZPath [v] [] |}.
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

#[export] Instance ZGraph_singlepath : SinglePath ZGraph Z (Z*Z) ZPath ZGraph_path.
Proof.
  refine {| single_path := fun u v e => mkZPath [u; v] [e] |}.
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

Definition zconcat (a1 a2: ZPath): ZPath :=
  mkZPath (zpv a1 ++ tl (zpv a2)) (zpe a1 ++ zpe a2).

(* nth_error of an append where index lands in the first part. *)
Lemma nth_error_app_l {A: Type} (l1 l2: list A) (n: nat):
  (n < length l1)%nat -> nth_error (l1 ++ l2) n = nth_error l1 n.
Proof.
  revert n. induction l1 as [|x xs IH]; intros n Hn; simpl in *.
  - lia.
  - destruct n as [|n']; simpl; auto. apply IH. lia.
Qed.

#[export] Instance ZGraph_concatpath : ConcatPath ZGraph Z (Z*Z) ZPath ZGraph_path.
Proof.
  refine {| concat_path := zconcat |}.
  - (* concat_path_valid *)
    intros g a1 a2 [Hnn1 Hcoh1] [Hnn2 Hcoh2] Htail.
    destruct Hcoh1 as [Hlen1 Hstep1].
    destruct Hcoh2 as [Hlen2 Hstep2].
    (* tail a1 = head a2 : last (zpv a1) 0 = hd 0 (zpv a2) *)
    simpl in Htail.
    split.
    + (* non-empty *)
      unfold zconcat. simpl.
      destruct (zpv a1); [congruence|]. discriminate.
    + unfold zconcat. constructor.
      * (* length *)
        simpl. rewrite !length_app.
        (* length (tl pv2) = length pv2 - 1, and pv2 nonempty *)
        destruct (zpv a2) as [|y2 ys2] eqn:Hv2; [congruence|].
        simpl in Hlen2 |- *. rewrite Hlen1. lia.
      * (* step coherence *)
        intros n u v e Hn He Hu Hv.
        simpl (length _) in Hn. simpl (zpe _) in *. simpl (zpv _) in Hu, Hv.
        rewrite length_app in Hn.
        (* split on whether edge index n is in first edge list *)
        destruct (Nat.ltb_spec n (length (zpe a1))) as [Hlt | Hge].
        -- (* in first part: indices into pv1 region *)
           rewrite nth_error_app_l in He by auto.
           (* vertex indices n and S n are both < length pv1 *)
           assert (Hn_v: (n < length (zpv a1))%nat) by lia.
           assert (HSn_v: (S n < length (zpv a1))%nat) by lia.
           rewrite nth_error_app_l in Hu by auto.
           rewrite nth_error_app_l in Hv by auto.
           apply (Hstep1 n u v e); auto. lia.
        -- (* in second part *)
           rewrite nth_error_app2 in He by auto.
           set (m := (n - length (zpe a1))%nat) in *.
           assert (Hm: (m < length (zpe a2))%nat) by (unfold m; lia).
           (* relate vertex positions in (pv1 ++ tl pv2) to those of pv2 *)
           destruct (zpv a2) as [|y2 ys2] eqn:Hv2; [congruence|].
           simpl (tl _) in Hu, Hv.
           set (L1 := length (zpv a1)) in *.
           assert (HL1: L1 = S (length (zpe a1))) by (unfold L1; lia).
           assert (Hn_eq: n = (L1 - 1 + m)%nat) by (unfold m; lia).
           (* The S n vertex lands in ys2 cleanly. *)
           assert (HvSn: nth_error (zpv a2) (S m) = Some v).
           { rewrite nth_error_app2 in Hv by (unfold L1 in *; lia).
             rewrite Hv2. simpl.
             replace (S n - length (zpv a1))%nat with m in Hv
               by (unfold L1 in *; lia). exact Hv. }
           (* The n-th vertex: either last of pv1 (m=0) or inside ys2. *)
           assert (Hvn: nth_error (zpv a2) m = Some u).
           { destruct m as [|m'] eqn:Hmeq.
             - (* m = 0: index n = L1-1, the last vertex of pv1 *)
               assert (HnL1: n = (L1 - 1)%nat) by lia.
               rewrite nth_error_app_l in Hu by (unfold L1 in *; lia).
               (* nth_error pv1 (L1-1) = tl_error pv1 = Some (last pv1 0) *)
               assert (Htl1: tl_error (zpv a1) = Some u).
               { unfold tl_error. replace (length (zpv a1) - 1)%nat
                   with n by (unfold L1 in HnL1; lia). exact Hu. }
               rewrite (tl_error_last 0) in Htl1 by auto.
               (* last pv1 0 = tail a1 = head a2 = y2 *)
               inversion Htl1 as [Hlast].
               rewrite Htail in Hlast. simpl in Hlast.
               rewrite Hv2. simpl. congruence.
             - (* m >= 1: index n lands in ys2 *)
               assert (Hnge: (n >= L1)%nat) by lia.
               rewrite nth_error_app2 in Hu by (unfold L1 in *; lia).
               rewrite Hv2. simpl.
               replace (n - length (zpv a1))%nat with m' in Hu
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

Definition zdestruct_1n (g: ZGraph) (p: ZPath)
  (H: zpath_valid g p) : @PathConsView ZPath (Z*Z) Z :=
  match zpe p with
  | [] => DestructBase1n (hd 0 (zpv p))
  | e :: es =>
      DestructStep1n (mkZPath (tl (zpv p)) es)
                     (hd 0 (zpv p)) (hd 0 (tl (zpv p))) e
  end.

#[export] Instance ZGraph_destruct1npath :
  Destruct1nPath ZGraph Z (Z*Z) ZPath ZGraph_path
    ZGraph_emptypath ZGraph_singlepath ZGraph_concatpath.
Proof.
  refine {| destruct_1n_path := zdestruct_1n |}.
  intros g p Hvalid.
  unfold path_cons_spec, zdestruct_1n.
  destruct Hvalid as [Hnn Hcoh].
  destruct Hcoh as [Hlen Hstep].
  destruct p as [pv pe]. simpl in *.
  destruct pe as [|e es]; simpl in *.
  - (* base: pe = [], so pv has length 1 *)
    destruct pv as [|v0 vs]; [congruence|].
    simpl in Hlen.
    assert (vs = []) by (destruct vs; simpl in Hlen; [reflexivity|lia]).
    subst vs. simpl.
    (* empty_path v0 = mkZPath [v0] [] *)
    reflexivity.
  - (* step: pe = e :: es, pv = u :: v1 :: vs *)
    destruct pv as [|u tlpv]; [congruence|].
    destruct tlpv as [|v1 vs]; simpl in Hlen; [lia|].
    simpl.
    split; [|split; [|split]].
    + (* path_valid g (mkZPath (v1::vs) es) *)
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
    + (* head (mkZPath (v1::vs) es) = v1 *)
      reflexivity.
    + (* step_aux g e u v1 *)
      apply (Hstep 0%nat u v1 e).
      * simpl. lia.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + (* mkZPath (u::v1::vs) (e::es)
           = concat_path (single_path u v1 e) (mkZPath (v1::vs) es) *)
      reflexivity.
Qed.

(* ============================================================ *)
(*  DEMO: the GraphLib predicates are now usable on ZGraph.      *)
(* ============================================================ *)

Definition demo_vpath (g : ZGraph) (u v : Z) (l : list Z) : Prop :=
  valid_vpath g u l v.

Definition demo_reach (g : ZGraph) (u v : Z) : Prop :=
  reachable g u v.

Definition demo_simple (g : ZGraph) (p : ZPath) (u v : Z) : Prop :=
  is_simple_path g p u v.

(* Sanity: the empty single-vertex path is a valid vpath from v to v. *)
Example demo_vpath_empty (g : ZGraph) (v : Z) : demo_vpath g v v [v].
Proof. unfold demo_vpath. apply valid_vpath_empty. Qed.
