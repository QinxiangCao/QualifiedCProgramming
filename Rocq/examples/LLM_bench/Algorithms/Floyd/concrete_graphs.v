Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import ListLib.Base.Positional.
From AUXLib Require Import EqDec ListLib.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
From GraphLib Require Import path path_basic.
Require Import GraphLib.reachable.Zweight.
From SumLib Require Import ZRange.

Import ListNotations.
Local Open Scope Z_scope.

(** Integer-indexed weighted directed graphs used by the Floyd C examples.
    The C matrix stores [infinity] for absent edges; all other cells are
    interpreted as concrete edge distances. *)
Module FloydGraph.

Definition V : Type := Z.
Definition E : Type := (Z * Z)%type.

Definition max_vertices : Z := 10.
Definition infinity : Z := 1000000000.

Record G : Type := mkG {
  vertex_count : Z;
  edge_weight : V -> V -> option Z;
}.

Definition vertex_valid (g : G) (v : V) : Prop :=
  0 <= v < vertex_count g.

Definition graph_step (g : G) (u v : V) : Prop :=
  vertex_valid g u /\
  vertex_valid g v /\
  exists w, edge_weight g u v = Some w.

Definition edge_valid (g : G) (e : E) : Prop :=
  graph_step g (fst e) (snd e).

Definition graph_wf (g : G) : Prop :=
  0 <= vertex_count g <= max_vertices.

Definition vertices (g : G) : list V :=
  Zrange 0 (vertex_count g).

Definition matrix_shape (n : Z) (rows : list (list Z)) : Prop :=
  Zlength rows = n /\
  forall i, 0 <= i < n -> Zlength (Znth i rows nil) = n.

Definition cell_value_safe (x : Z) : Prop :=
  -infinity <= x <= infinity.

Definition matrix_values_safe (n : Z) (rows : list (list Z)) : Prop :=
  forall i j,
    0 <= i < n ->
    0 <= j < n ->
    cell_value_safe (Znth j (Znth i rows nil) infinity).

Definition cell_as_distance (x : Z) : option Z :=
  if Z.eq_dec x infinity then None else Some x.

Definition distance_as_cell (d : option Z) : Z :=
  match d with
  | Some x => x
  | None => infinity
  end.

Definition matrix_distance (rows : list (list Z)) (u v : Z) : option Z :=
  cell_as_distance (Znth v (Znth u rows nil) infinity).

Definition matrix_graph_model (g : G) (rows : list (list Z)) : Prop :=
  graph_wf g /\
  matrix_shape max_vertices rows /\
  matrix_values_safe max_vertices rows /\
  forall u v,
    vertex_valid g u ->
    vertex_valid g v ->
    edge_weight g u v = matrix_distance rows u v.

#[export] Instance edge_eqdec : EqDec E eq.
Proof.
  intros [u1 v1] [u2 v2].
  destruct (Z.eq_dec u1 u2) as [Hu | Hu].
  - destruct (Z.eq_dec v1 v2) as [Hv | Hv].
    + left. subst. reflexivity.
    + right. intros H. inversion H. contradiction.
  - right. intros H. inversion H. contradiction.
Defined.

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

#[export] Instance stepunique_instance : StepUniqueDirected G V E.
Proof.
  constructor.
  intros g e x1 y1 x2 y2 Hg [He1 _] [He2 _].
  rewrite He1 in He2; inversion He2; auto.
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

#[export] Instance weight_instance : EdgeWeight G E := {|
  weight := fun g e => edge_weight g (fst e) (snd e)
|}.

Record PathData : Type := mkPathData {
  path_vertices : list V;
  path_edges : list E;
}.

Lemma hd_error_hd {A : Type} (d : A) (xs : list A) :
  xs <> nil -> hd_error xs = Some (hd d xs).
Proof.
  destruct xs; [congruence | reflexivity].
Qed.

Lemma tl_error_last {A : Type} (d : A) (xs : list A) :
  xs <> nil -> tl_error xs = Some (last xs d).
Proof.
  intros Hnn.
  pose proof (app_removelast_last d Hnn) as Heq.
  transitivity (tl_error (removelast xs ++ [last xs d])).
  { f_equal. exact Heq. }
  rewrite Positional.tl_error_last. reflexivity.
Qed.

Definition path_valid_prop (g : G) (p : PathData) : Prop :=
  path_vertices p <> nil /\
  vpath_iff_epath_prop g (path_vertices p) (path_edges p).

#[export] Instance path_instance : Path G V E PathData.
Proof.
  refine {|
    path_valid := path_valid_prop;
    vertex_in_path := path_vertices;
    head := fun p => hd 0 (path_vertices p);
    tail := fun p => last (path_vertices p) 0;
    edge_in_path := path_edges;
  |}.
  - intros g p [Hnn _]. symmetry. apply hd_error_hd; auto.
  - intros g p [Hnn _]. symmetry. apply tl_error_last; auto.
  - intros g p [_ Hcoh]. exact Hcoh.
Defined.

#[export] Instance empty_path_instance :
  EmptyPath G V E PathData path_instance.
Proof.
  refine {| empty_path := fun v => mkPathData [v] [] |}.
  - intros g v. split.
    + discriminate.
    + constructor.
      * reflexivity.
      * intros n u v0 e Hn _ _ _. simpl in Hn. lia.
  - reflexivity.
Defined.

#[export] Instance single_path_instance :
  SinglePath G V E PathData path_instance.
Proof.
  refine {| single_path := fun u v e => mkPathData [u; v] [e] |}.
  - intros g u v e Hstep. split.
    + discriminate.
    + constructor.
      * reflexivity.
      * intros n u0 v0 e0 Hn He Hu Hv. simpl in Hn.
        assert (n = 0%nat) by lia. subst n.
        simpl in He, Hu, Hv.
        inversion He; inversion Hu; inversion Hv; subst.
        exact Hstep.
  - reflexivity.
  - reflexivity.
Defined.

Definition concat_path_data (p1 p2 : PathData) : PathData :=
  mkPathData
    (path_vertices p1 ++ tl (path_vertices p2))
    (path_edges p1 ++ path_edges p2).

Lemma nth_error_app_l {A : Type} (xs ys : list A) (n : nat) :
  (n < length xs)%nat -> nth_error (xs ++ ys) n = nth_error xs n.
Proof.
  revert n.
  induction xs as [| x xs IH]; intros n Hn; simpl in *.
  - lia.
  - destruct n; simpl; auto. apply IH. lia.
Qed.

#[export] Instance concat_path_instance :
  ConcatPath G V E PathData path_instance.
Proof.
  refine {| concat_path := concat_path_data |}.
  - intros g p1 p2 [Hnn1 Hcoh1] [Hnn2 Hcoh2] Htail.
    destruct Hcoh1 as [Hlen1 Hstep1].
    destruct Hcoh2 as [Hlen2 Hstep2].
    simpl in Htail.
    split.
    + unfold concat_path_data. simpl.
      destruct (path_vertices p1); [congruence | discriminate].
    + unfold concat_path_data. constructor.
      * simpl. rewrite !length_app.
        destruct (path_vertices p2) as [| v2 vs2] eqn:Hv2;
          [congruence |].
        simpl in Hlen2 |- *. rewrite Hlen1. lia.
      * intros n u v e Hn He Hu Hv.
        simpl (length _) in Hn.
        simpl (path_edges _) in *.
        simpl (path_vertices _) in Hu, Hv.
        rewrite length_app in Hn.
        destruct (Nat.ltb_spec n (length (path_edges p1))) as [Hlt | Hge].
        -- rewrite nth_error_app_l in He by auto.
           assert (Hn_v : (n < length (path_vertices p1))%nat) by lia.
           assert (HSn_v : (S n < length (path_vertices p1))%nat) by lia.
           rewrite nth_error_app_l in Hu by auto.
           rewrite nth_error_app_l in Hv by auto.
           apply (Hstep1 n u v e); auto. lia.
        -- rewrite nth_error_app2 in He by auto.
           set (m := (n - length (path_edges p1))%nat) in *.
           assert (Hm : (m < length (path_edges p2))%nat) by
             (unfold m; lia).
           destruct (path_vertices p2) as [| v2 vs2] eqn:Hv2;
             [congruence |].
           simpl (tl _) in Hu, Hv.
           set (L1 := length (path_vertices p1)) in *.
           assert (HL1 : L1 = S (length (path_edges p1))) by
             (unfold L1; lia).
           assert (HvSn : nth_error (path_vertices p2) (S m) = Some v).
           {
             rewrite nth_error_app2 in Hv by (unfold L1 in *; lia).
             rewrite Hv2. simpl.
             replace (S n - length (path_vertices p1))%nat with m in Hv
               by (unfold L1 in *; lia).
             exact Hv.
           }
           assert (Hvn : nth_error (path_vertices p2) m = Some u).
           {
             destruct m as [| m'] eqn:Hmeq.
             - assert (HnL1 : n = (L1 - 1)%nat) by lia.
               rewrite nth_error_app_l in Hu by (unfold L1 in *; lia).
               assert (Htl1 : tl_error (path_vertices p1) = Some u).
               {
                 unfold tl_error.
                 replace (length (path_vertices p1) - 1)%nat with n
                   by (unfold L1 in HnL1; lia).
                 exact Hu.
               }
               rewrite (tl_error_last 0) in Htl1 by auto.
               inversion Htl1 as [Hlast_eq]; clear Htl1.
               rewrite Hv2. simpl. f_equal.
               simpl in Htail.
               rewrite <- Htail. reflexivity.
             - assert (Hnge : (n >= L1)%nat) by lia.
               rewrite nth_error_app2 in Hu by (unfold L1 in *; lia).
               rewrite Hv2. simpl.
               replace (n - length (path_vertices p1))%nat with m' in Hu
                 by (unfold L1 in *; lia).
               exact Hu.
           }
           rewrite Hv2 in Hvn, HvSn.
           apply (Hstep2 m u v e).
           ++ lia.
           ++ exact He.
           ++ exact Hvn.
           ++ exact HvSn.
  - reflexivity.
  - reflexivity.
Defined.

Definition destruct_path_1n
    (g : G) (p : PathData) (H : path_valid_prop g p)
    : @PathConsView PathData E V :=
  match path_edges p with
  | [] => DestructBase1n (hd 0 (path_vertices p))
  | e :: es =>
      DestructStep1n
        (mkPathData (tl (path_vertices p)) es)
        (hd 0 (path_vertices p))
        (hd 0 (tl (path_vertices p)))
        e
  end.

#[export] Instance destruct1n_path_instance :
  Destruct1nPath G V E PathData path_instance
    empty_path_instance single_path_instance concat_path_instance.
Proof.
  refine {| destruct_1n_path := destruct_path_1n |}.
  intros g p Hvalid.
  unfold path_cons_spec, destruct_path_1n.
  destruct Hvalid as [Hnn Hcoh].
  destruct Hcoh as [Hlen Hstep].
  destruct p as [vs es]. simpl in *.
  destruct es as [| e es]; simpl in *.
  - destruct vs as [| v0 vs]; [congruence |].
    simpl in Hlen.
    assert (vs = []) by (destruct vs; simpl in Hlen; [reflexivity | lia]).
    subst vs. simpl. reflexivity.
  - destruct vs as [| u rest]; [congruence |].
    destruct rest as [| v1 vs]; simpl in Hlen; [lia |].
    simpl.
    split; [| split; [| split]].
    + split; [discriminate |].
      constructor.
      * simpl. simpl in Hlen. lia.
      * intros n u0 v0 e0 Hn He0 Hu0 Hv0.
        simpl in Hn, He0, Hu0, Hv0.
        apply (Hstep (S n) u0 v0 e0).
        -- simpl. lia.
        -- simpl. exact He0.
        -- simpl. exact Hu0.
        -- simpl. exact Hv0.
    + reflexivity.
    + apply (Hstep 0%nat u v1 e).
      * simpl. lia.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

Lemma step_iff : forall g u v,
  step g u v <-> graph_step g u v.
Proof.
  intros g u v. unfold step; split.
  - intros [[x y] [He Hstep]].
    inversion He; exact Hstep.
  - intros Hstep. exists (u, v). split; [reflexivity | exact Hstep].
Qed.

End FloydGraph.
