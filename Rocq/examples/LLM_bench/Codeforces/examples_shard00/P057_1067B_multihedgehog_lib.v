Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.vpath.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.
Import ListNotations.
Local Open Scope Z_scope.

Definition Degree (e : list (Z * Z)) (v : Z) : Z :=
  Zlength (filter (fun p => orb (Z.eqb (fst p) v) (Z.eqb (snd p) v)) e).

Definition HedgehogGraph (e : list (Z * Z)) : ZGraph :=
  {| zv := fun _ => True;
     ze := fun x y => In (x,y) e \/ In (y,x) e |}.

Definition HedgehogPath (e : list (Z * Z)) (u v : Z) (path : list Z) : Prop :=
  valid_vpath (HedgehogGraph e) u path v /\ NoDup path.

Definition CanonicalEdge (edge : Z * Z) : Z * Z :=
  if Z.leb (fst edge) (snd edge) then edge else (snd edge, fst edge).

Definition CurrentEdgeFresh (edges : list (Z * Z)) (index : Z) : Prop :=
  0 <= index < Zlength edges ->
  let edge := Znth index edges (0, 0) in
  fst edge <> snd edge /\
  ~ In (CanonicalEdge edge)
      (map CanonicalEdge (sublist 0 index edges)).

Definition TreeInput (n : Z) (e : list (Z * Z)) : Prop :=
  1 <= n <= 100000 /\ Zlength e = n - 1 /\
  Forall (fun p => 1 <= fst p <= n /\ 1 <= snd p <= n /\ fst p <> snd p) e /\
  (forall index, CurrentEdgeFresh e index) /\
  forall v, 1 <= v <= n -> exists path, HedgehogPath e 1 v path.

Definition AdjacencyNext (next_data : list Z) (from to : Z) : Prop :=
  0 <= from < Zlength next_data /\
  to = Znth from next_data (-1).

Definition AdjacencySlot
    (head_data next_data : list Z) (u slot : Z) : Prop :=
  0 <= u < Zlength head_data /\
  0 <= slot < Zlength next_data /\
  clos_refl_trans (AdjacencyNext next_data)
    (Znth u head_data (-1)) slot.

Definition AdjacencyBuildState
    (n : Z) (edges : list (Z * Z)) (done : Z)
    (head_data to_data next_data : list Z) : Prop :=
  0 <= done <= Zlength edges /\
  Zlength head_data = n /\
  Zlength to_data = 2 * done /\
  Zlength next_data = 2 * done /\
  (forall u, 0 <= u < n ->
    Znth u head_data (-1) = -1 \/
    0 <= Znth u head_data (-1) < 2 * done) /\
  (forall slot, 0 <= slot < 2 * done ->
    0 <= Znth slot to_data 0 < n /\
    (Znth slot next_data (-1) = -1 \/
     0 <= Znth slot next_data (-1) < slot)) /\
  (forall u v,
    0 <= u < n -> 0 <= v < n ->
    (In (u + 1, v + 1) (sublist 0 done edges) \/
     In (v + 1, u + 1) (sublist 0 done edges) <->
     exists slot,
       AdjacencySlot head_data next_data u slot /\
       Znth slot to_data 0 = v)) /\
  forall u slot1 slot2,
    AdjacencySlot head_data next_data u slot1 ->
    AdjacencySlot head_data next_data u slot2 ->
    Znth slot1 to_data 0 = Znth slot2 to_data 0 ->
    slot1 = slot2.

Definition AdjacencyModel
    (n : Z) (edges : list (Z * Z))
    (head_data to_data next_data : list Z) : Prop :=
  Zlength head_data = n /\
  Zlength to_data = 2 * n - 2 /\
  Zlength next_data = 2 * n - 2 /\
  Zlength edges = n - 1 /\
  (forall u, 0 <= u < n ->
    Znth u head_data (-1) = -1 \/
    0 <= Znth u head_data (-1) < 2 * n - 2) /\
  (forall slot, 0 <= slot < 2 * n - 2 ->
    0 <= Znth slot to_data 0 < n /\
    (Znth slot next_data (-1) = -1 \/
     0 <= Znth slot next_data (-1) < slot)) /\
  (forall u v,
    0 <= u < n -> 0 <= v < n ->
    (In (u + 1, v + 1) edges \/ In (v + 1, u + 1) edges <->
     exists slot,
       AdjacencySlot head_data next_data u slot /\
       Znth slot to_data 0 = v)) /\
  forall u slot1 slot2,
    AdjacencySlot head_data next_data u slot1 ->
    AdjacencySlot head_data next_data u slot2 ->
    Znth slot1 to_data 0 = Znth slot2 to_data 0 ->
    slot1 = slot2.

Definition DegreePrefix
    (n : Z) (edges : list (Z * Z)) (done : Z)
    (degrees : list Z) : Prop :=
  Zlength degrees = n /\
  forall v, 0 <= v < n ->
    Znth v degrees 0 = Degree (sublist 0 done edges) (v + 1).

Definition GraphDistance
    (edges : list (Z * Z)) (source vertex distance : Z) : Prop :=
  exists path,
    HedgehogPath edges source vertex path /\
    distance = Zlength path - 1 /\
    forall other,
      HedgehogPath edges source vertex other ->
      Zlength path <= Zlength other.

Definition HedgehogVertexOK
    (k center vertex distance degree : Z) : Prop :=
  distance <= k /\
  (distance = k -> degree = 1) /\
  (distance < k ->
    (vertex = center -> 3 <= degree) /\
    (vertex <> center -> 4 <= degree)).

Definition HedgehogLayers (n k center : Z) (e : list (Z * Z)) : Prop :=
  1 <= center <= n /\
  forall vertex, 1 <= vertex <= n ->
    exists distance,
      GraphDistance e center vertex distance /\
      HedgehogVertexOK k (center - 1) (vertex - 1)
        distance (Degree e vertex).

Definition Spec (n k : Z) (e : list (Z * Z)) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> exists center, HedgehogLayers n k center e).

Definition BFSParentState
    (n : Z) (edges : list (Z * Z)) (source : Z)
    (parents distances : list Z) : Prop :=
  Znth source parents (-1) = -1 /\
  forall v, 0 <= v < n -> v <> source ->
    0 <= Znth v distances (-1) ->
    0 <= Znth v parents (-1) < n /\
    (In (v + 1, Znth v parents (-1) + 1) edges \/
     In (Znth v parents (-1) + 1, v + 1) edges) /\
    Znth v distances (-1) = Znth (Znth v parents (-1)) distances (-1) + 1.

Definition BFSData
    (n : Z) (edges : list (Z * Z)) (source : Z)
    (parents distances : list Z) : Prop :=
  Zlength parents = n /\
  Zlength distances = n /\
  0 <= source < n /\
  BFSParentState n edges source parents distances /\
  (forall v, 0 <= v < n ->
    GraphDistance edges (source + 1) (v + 1) (Znth v distances (-1))).

Definition BFSResult
    (n : Z) (edges : list (Z * Z)) (source : Z)
    (parents distances : list Z) (farthest : Z) : Prop :=
  BFSData n edges source parents distances /\
  0 <= farthest < n /\
  forall v, 0 <= v < n ->
    Znth v distances (-1) <= Znth farthest distances (-1).

Definition BFSQueueState
    (n : Z) (edges : list (Z * Z)) (source processed farthest : Z)
    (queue parents distances : list Z) : Prop :=
  Zlength parents = n /\
  Zlength distances = n /\
  0 <= processed <= Zlength queue /\
  1 <= Zlength queue <= n /\
  NoDup queue /\
  Znth 0 queue 0 = source /\
  0 <= source < n /\
  0 <= farthest < n /\
  BFSParentState n edges source parents distances /\
  (forall q, 0 <= q < Zlength queue ->
    0 <= Znth q queue 0 < n /\
    0 <= Znth (Znth q queue 0) distances (-1)) /\
  (forall v, 0 <= v < n ->
    (In v queue <-> 0 <= Znth v distances (-1))) /\
  (forall q, 0 <= q < processed ->
    Znth (Znth q queue 0) distances (-1) <=
    Znth farthest distances (-1)) /\
  (forall q neighbor, 0 <= q < processed ->
    (In (Znth q queue 0 + 1, neighbor + 1) edges \/
     In (neighbor + 1, Znth q queue 0 + 1) edges) ->
    In neighbor queue) /\
  forall v, 0 <= v < n ->
    0 <= Znth v distances (-1) ->
    GraphDistance edges (source + 1) (v + 1) (Znth v distances (-1)).

Definition BFSFrontierState
    (n : Z) (edges : list (Z * Z)) (source vertex : Z)
    (distances : list Z) : Prop :=
  forall neighbor,
    0 <= neighbor < n ->
    (In (vertex + 1, neighbor + 1) edges \/
     In (neighbor + 1, vertex + 1) edges) ->
    Znth neighbor distances (-1) < 0 ->
    GraphDistance edges (source + 1) (neighbor + 1)
      (Znth vertex distances (-1) + 1).

Definition BFSFrontierComplete (n : Z) (edges : list (Z * Z)) : Prop :=
  forall source processed farthest queue parents distances,
    BFSQueueState n edges source processed farthest queue parents distances ->
    processed < Zlength queue ->
    BFSFrontierState n edges source (Znth processed queue 0) distances.

Definition AdjacencyScanState
    (head_data to_data next_data : list Z) (vertex cursor : Z)
    (queue : list Z) : Prop :=
  forall slot,
    AdjacencySlot head_data next_data vertex slot ->
    clos_refl_trans (AdjacencyNext next_data) cursor slot \/
    In (Znth slot to_data 0) queue.

Definition BFSAdjState
    (n : Z) (edges : list (Z * Z)) (source processed farthest : Z)
    (queue parents distances head_data to_data next_data : list Z)
    (vertex cursor : Z) : Prop :=
  BFSQueueState n edges source (processed - 1) farthest queue parents distances /\
  0 < processed <= Zlength queue /\
  vertex = Znth (processed - 1) queue 0 /\
  Znth vertex distances (-1) <= Znth farthest distances (-1) /\
  (-1 <= cursor < 2 * n - 2) /\
  (cursor = -1 \/ AdjacencySlot head_data next_data vertex cursor) /\
  (cursor <> -1 -> 0 <= Znth cursor to_data 0 < n) /\
  BFSFrontierState n edges source vertex distances /\
  AdjacencyScanState head_data to_data next_data vertex cursor queue /\
  (cursor = -1 ->
    forall neighbor,
      (In (vertex + 1, neighbor + 1) edges \/
       In (neighbor + 1, vertex + 1) edges) ->
      In neighbor queue).

Definition AncestorAfter
    (parents : list Z) (start steps vertex : Z) : Prop :=
  exists path,
    Zlength path = steps + 1 /\
    Znth 0 path 0 = start /\
    Znth steps path 0 = vertex /\
    forall i, 0 <= i < steps ->
      Znth (i + 1) path 0 = Znth (Znth i path 0) parents (-1).

Definition DecisionPrefix
    (n k center done ok : Z) (degrees distances : list Z) : Prop :=
  (ok = 0 \/ ok = 1) /\
  (ok = 1 <->
    forall v, 0 <= v < done ->
      HedgehogVertexOK k center v
        (Znth v distances (-1)) (Znth v degrees 0)).

Definition DiameterDecision
    (k : Z) (second_dist : list Z) (endpoint out : Z) : Prop :=
  (out = 0 /\ Znth endpoint second_dist 0 <> 2 * k) \/
  (out = 1 /\ Znth endpoint second_dist 0 = 2 * k).

Definition SolverDecision
    (n k : Z) (edges : list (Z * Z))
    (second_parent second_dist : list Z) (endpoint center : Z)
    (center_parent center_dist degrees : list Z) (done out : Z) : Prop :=
  (out = 0 /\ Znth endpoint second_dist 0 <> 2 * k) \/
  (Znth endpoint second_dist 0 = 2 * k /\
   AncestorAfter second_parent endpoint k center /\
   BFSData n edges center center_parent center_dist /\
   DecisionPrefix n k center done out degrees center_dist).

Definition SolverCertificate
    (n k : Z) (edges : list (Z * Z))
    (first_parent first_dist : list Z) (first_endpoint : Z)
    (second_parent second_dist : list Z) (second_endpoint center : Z)
    (center_parent center_dist degrees : list Z) (out : Z) : Prop :=
  BFSResult n edges 0 first_parent first_dist first_endpoint /\
  BFSResult n edges first_endpoint second_parent second_dist second_endpoint /\
  DegreePrefix n edges (n - 1) degrees /\
  SolverDecision n k edges second_parent second_dist second_endpoint center
    center_parent center_dist degrees n out.

Definition HedgehogDecisionComplete
    (n k : Z) (edges : list (Z * Z)) : Prop :=
  forall first_parent first_dist first_endpoint
         second_parent second_dist second_endpoint center
         center_parent center_dist degrees,
    BFSResult n edges 0 first_parent first_dist first_endpoint ->
    BFSResult n edges first_endpoint second_parent second_dist second_endpoint ->
    DegreePrefix n edges (n - 1) degrees ->
    SolverDecision n k edges second_parent second_dist second_endpoint center
      center_parent center_dist degrees n 0 ->
    ~ exists candidate, HedgehogLayers n k candidate edges.

Definition GraphPre (n : Z) (e : list (Z * Z)) : Prop :=
  TreeInput n e /\
  BFSFrontierComplete n e /\
  forall k, 1 <= k <= 1000000000 -> HedgehogDecisionComplete n k e.

Definition Pre (n k : Z) (e : list (Z * Z)) : Prop :=
  1 <= k <= 1000000000 /\ GraphPre n e.

Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Lemma Zlength_filter_le__bounds_safety :
  forall {A : Type} (f : A -> bool) (xs : list A),
    Zlength (filter f xs) <= Zlength xs.
Proof.
  intros A f xs; induction xs as [|x xs IH]; simpl.
  - lia.
  - destruct (f x); simpl; rewrite ?Zlength_cons in *; lia.
Qed.
Lemma Zlength_Zrange__bounds_safety :
  forall lo hi, lo <= hi -> Zlength (Zrange lo hi) = hi - lo.
Proof.
  intros lo hi Hrange.
  unfold Zrange.
  rewrite Zlength_correct.
  assert (Haux : forall start count,
      length (Zrange_aux start count) = count).
  { intros start count. revert start.
    induction count as [|count IH]; intros start; simpl; auto. }
  rewrite Haux.
  lia.
Qed.
Lemma edge_endpoints_bounds__bounds_safety :
  forall n edges x y,
    TreeInput n edges ->
    (In (x, y) edges \/ In (y, x) edges) ->
    1 <= x <= n /\ 1 <= y <= n.
Proof.
  intros n edges x y Htree Hedge.
  unfold TreeInput in Htree.
  destruct Htree as [_ [_ [Hends _]]].
  destruct Hedge as [Hxyin | Hyxin].
  - apply Forall_forall with (x := (x, y)) in Hends as Hxy; auto.
    simpl in Hxy; exact (conj (proj1 Hxy) (proj1 (proj2 Hxy))).
  - apply Forall_forall with (x := (y, x)) in Hends as Hyx; auto.
    simpl in Hyx; exact (conj (proj1 (proj2 Hyx)) (proj1 Hyx)).
Qed.
Lemma valid_vpath_members_bounds__bounds_safety :
  forall n edges source path target,
    TreeInput n edges ->
    1 <= source <= n ->
    valid_vpath (HedgehogGraph edges) source path target ->
    forall x, In x path -> 1 <= x <= n.
Proof.
  intros n edges source path.
  revert source.
  induction path as [|first rest IH]; intros source target Htree Hsource Hpath x Hx.
  - exfalso. eapply valid_vpath_not_nil; eauto.
  - pose proof (valid_vpath_start _ _ _ _ Hpath) as [tail Heq].
    inversion Heq; subst first tail.
    apply valid_vpath_cons_inv in Hpath.
    destruct Hpath as [[Hnil _] | [next [Hstep Htail]]].
    + subst rest. simpl in Hx. destruct Hx as [-> | []]. exact Hsource.
    + simpl in Hx. destruct Hx as [-> | Hx].
      * exact Hsource.
      * apply IH with (source := next) (target := target); auto.
        destruct Hstep as [edge Hstep].
        simpl in Hstep.
        unfold zstep_aux in Hstep.
        destruct Hstep as [Heqsource [Heqnext [Hedge _]]].
        subst source next.
        pose proof (edge_endpoints_bounds__bounds_safety n edges
          (fst edge) (snd edge) Htree Hedge) as [_ Hnext].
        exact Hnext.
Qed.
Lemma graph_distance_bounds__bounds_safety :
  forall n edges source target distance,
    TreeInput n edges ->
    1 <= source <= n ->
    GraphDistance edges source target distance ->
    0 <= distance < n.
Proof.
  intros n edges source target distance Htree Hsource Hdist.
  unfold GraphDistance in Hdist.
  destruct Hdist as [path [[Hpath Hnodup] [Hdistance _]]].
  assert (Hincl : incl path (Zrange 1 (n + 1))).
  { intros x Hx. apply In_Zrange.
    pose proof (valid_vpath_members_bounds__bounds_safety n edges source path
      target Htree Hsource Hpath x Hx) as Hxbounds.
    lia. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite <- !Zlength_correct in Hlen.
  rewrite Zlength_Zrange__bounds_safety in Hlen by lia.
  pose proof (valid_vpath_not_nil _ _ _ _ Hpath) as Hnonempty.
  assert (1 <= Zlength path).
  { destruct path as [|first rest].
    - contradiction.
    - rewrite Zlength_cons. pose proof (Zlength_nonneg rest). lia. }
  lia.
Qed.
Lemma degree_prefix_bounds__bounds_safety :
  forall n edges done degrees vertex,
    DegreePrefix n edges done degrees ->
    0 <= done <= Zlength edges ->
    0 <= vertex < n ->
    0 <= Znth vertex degrees 0 <= done.
Proof.
  intros n edges done degrees vertex Hprefix Hdone Hvertex.
  unfold DegreePrefix in Hprefix.
  destruct Hprefix as [_ Hprefix].
  rewrite Hprefix by exact Hvertex.
  unfold Degree.
  pose proof (Zlength_nonneg
    (filter (fun p : Z * Z =>
       orb (Z.eqb (fst p) (vertex + 1)) (Z.eqb (snd p) (vertex + 1)))
      (sublist 0 done edges))) as Hnonneg.
  pose proof (Zlength_filter_le__bounds_safety
    (fun p : Z * Z =>
       orb (Z.eqb (fst p) (vertex + 1)) (Z.eqb (snd p) (vertex + 1)))
    (sublist 0 done edges)) as Hle.
  rewrite Zlength_sublist in Hle by lia.
  lia.
Qed.
Lemma graph_distance_zero_refl__bfs_initialization :
  forall edges source,
    GraphDistance edges source source 0.
Proof.
  intros edges source.
  unfold GraphDistance.
  exists (source :: nil).
  split.
  - unfold HedgehogPath.
    split.
    + apply valid_vpath_empty.
    + constructor; [simpl; tauto | constructor].
  - split.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + intros other Hother.
      unfold HedgehogPath in Hother.
      destruct Hother as [Hvalid Hnodup].
      destruct other as [|x xs].
      * exfalso.
        pose proof (valid_vpath_not_nil
          (HedgehogGraph edges) source nil source Hvalid) as Hnotnil.
        apply Hnotnil. reflexivity.
      * rewrite !Zlength_cons, !Zlength_nil.
        pose proof (Zlength_nonneg xs).
        lia.
Qed.
Lemma In_Znth__bfs_queue_entry :
  forall (A : Type) (l : list A) (x d : A),
    In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  destruct (In_nth l x d Hin) as [i [Hi Heq]].
  exists (Z.of_nat i). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Heq.
Qed.
Lemma In_map_nat_seq__bfs_queue_entry : forall n x,
  0 <= n ->
  (0 <= x < n <->
   In x (map Z.of_nat (seq 0 (Z.to_nat n)))).
Proof.
  intros n x Hn. split.
  - intros Hx. apply in_map_iff.
    exists (Z.to_nat x). split; [lia |].
    apply in_seq. lia.
  - intros Hin. apply in_map_iff in Hin.
    destruct Hin as [i [Hxi Hi]].
    apply in_seq in Hi. lia.
Qed.
Lemma NoDup_map_nat_Z__bfs_queue_entry : forall l,
  NoDup l -> NoDup (map Z.of_nat l).
Proof.
  intros l Hnodup. induction Hnodup; simpl.
  - constructor.
  - constructor.
    + intro Hin. apply in_map_iff in Hin.
      destruct Hin as [y [Heq Hin]].
      assert (y = x) by lia. subst y. exact (H Hin).
    + exact IHHnodup.
Qed.
Lemma bounded_nodup_full__bfs_queue_entry :
  forall n (queue : list Z),
    0 <= n ->
    Zlength queue = n ->
    NoDup queue ->
    (forall i, 0 <= i < Zlength queue ->
      0 <= Znth i queue 0 < n) ->
    forall v, 0 <= v < n -> In v queue.
Proof.
  intros n queue Hn Hlen Hnodup Hbounds v Hv.
  assert (Hincl : incl queue (map Z.of_nat (seq 0 (Z.to_nat n)))).
  {
    intros x Hx.
    destruct (In_Znth__bfs_queue_entry Z queue x 0 Hx)
      as [i [Hi Hix]].
    apply (proj1 (In_map_nat_seq__bfs_queue_entry n x Hn)).
    specialize (Hbounds i Hi).
    rewrite Hix in Hbounds.
    exact Hbounds.
  }
  assert (Hperm : Permutation queue
    (map Z.of_nat (seq 0 (Z.to_nat n)))).
  {
    apply NoDup_Permutation_bis.
    - exact Hnodup.
    - rewrite length_map, length_seq.
      rewrite <- Hlen, Zlength_correct, Nat2Z.id.
      reflexivity.
    - exact Hincl.
  }
  eapply Permutation_in.
  - apply Permutation_sym. exact Hperm.
  - apply (proj1 (In_map_nat_seq__bfs_queue_entry n v Hn)). exact Hv.
Qed.
Lemma tree_edge_bounds__bfs_queue_entry :
  forall n edges u v,
    TreeInput n edges ->
    (In (u + 1, v + 1) edges \/ In (v + 1, u + 1) edges) ->
    0 <= u < n /\ 0 <= v < n.
Proof.
  intros n edges u v Htree Hedge.
  unfold TreeInput in Htree.
  destruct Htree as [_ [_ [Hvalid _]]].
  destruct Hedge as [Hedge | Hedge].
  - apply Forall_forall with (x := (u + 1, v + 1)) in Hvalid;
      [simpl in Hvalid; lia | exact Hedge].
  - apply Forall_forall with (x := (v + 1, u + 1)) in Hvalid;
      [simpl in Hvalid; lia | exact Hedge].
Qed.
Lemma adjacency_from_minus_one_impossible__bfs_queue_entry :
  forall next_data slot,
    0 <= slot ->
    clos_refl_trans (AdjacencyNext next_data) (-1) slot -> False.
Proof.
  intros next_data slot Hslot Hreach.
  unfold clos_refl_trans in Hreach. sets_unfold in Hreach.
  destruct Hreach as [steps Hsteps].
  destruct steps as [|steps].
  - simpl in Hsteps. sets_unfold in Hsteps. subst slot. lia.
  - simpl in Hsteps. sets_unfold in Hsteps.
    destruct Hsteps as [middle [Hedge _]].
    unfold AdjacencyNext in Hedge. lia.
Qed.
Lemma bfs_adj_entry__bfs_queue_entry :
  forall n edges source processed old_farthest new_farthest
    queue parents distances head_data to_data next_data,
    GraphPre n edges ->
    AdjacencyModel n edges head_data to_data next_data ->
    BFSQueueState n edges source processed old_farthest
      queue parents distances ->
    processed < Zlength queue ->
    0 <= new_farthest < n ->
    Znth (Znth processed queue 0) distances (-1) <=
      Znth new_farthest distances (-1) ->
    (forall q, 0 <= q < processed ->
      Znth (Znth q queue 0) distances (-1) <=
      Znth new_farthest distances (-1)) ->
    BFSAdjState n edges source (processed + 1) new_farthest
      queue parents distances head_data to_data next_data
      (Znth processed queue 0)
      (Znth (Znth processed queue 0) head_data 0).
Proof.
  intros n edges source processed old_farthest new_farthest
    queue parents distances head_data to_data next_data
    Hgraph Hmodel Hqueue Hprocessed Hnew Hcurrent Hprior.
  pose proof Hqueue as Hqueue_old.
  pose proof Hgraph as Hgraph_old.
  pose proof (proj1 Hgraph) as Htree.
  pose proof Hmodel as Hmodel_old.
  unfold BFSQueueState in Hqueue.
  destruct Hqueue as
    [Hparents [Hdistances [Hprocessed_bounds [Hqueue_bounds
    [Hnodup [Hsource_head [Hsource_bounds [Hold_bounds
    [Hparent_state [Hqueue_values [Hmembership [Hold_prior
    [Hprocessed_neighbors Hdist_graph]]]]]]]]]]]]].
  assert (Hvertex : 0 <= Znth processed queue 0 < n).
  { exact (proj1 (Hqueue_values processed ltac:(lia))). }
  unfold AdjacencyModel in Hmodel.
  destruct Hmodel as
    [Hhead_len [Hto_len [Hnext_len [Hedges_len [Hheads
    [Hslots [Hedge_slots Hslot_unique]]]]]]].
  assert (Hqueue_new : BFSQueueState n edges source processed new_farthest
    queue parents distances).
  {
    unfold BFSQueueState.
    exact (conj Hparents
      (conj Hdistances
      (conj Hprocessed_bounds
      (conj Hqueue_bounds
      (conj Hnodup
      (conj Hsource_head
      (conj Hsource_bounds
      (conj Hnew
      (conj Hparent_state
      (conj Hqueue_values
      (conj Hmembership
      (conj Hprior
      (conj Hprocessed_neighbors Hdist_graph))))))))))))).
  }
  assert (Hhead_range :
    -1 <= Znth (Znth processed queue 0) head_data 0 < 2 * n - 2).
  {
    specialize (Hheads (Znth processed queue 0) Hvertex).
    rewrite (Znth_indep head_data (Znth processed queue 0) (-1) 0)
      in Hheads by (rewrite Hhead_len; exact Hvertex).
    destruct Hheads; lia.
  }
  assert (Hhead_slot :
    Znth (Znth processed queue 0) head_data 0 = -1 \/
    AdjacencySlot head_data next_data (Znth processed queue 0)
      (Znth (Znth processed queue 0) head_data 0)).
  {
    specialize (Hheads (Znth processed queue 0) Hvertex).
    rewrite (Znth_indep head_data (Znth processed queue 0) (-1) 0)
      in Hheads by (rewrite Hhead_len; exact Hvertex).
    destruct Hheads as [Hminus | Hhead_bounds].
    - left. exact Hminus.
    - right. unfold AdjacencySlot.
      assert (Hvhead : 0 <= Znth processed queue 0 < Zlength head_data)
        by (rewrite Hhead_len; exact Hvertex).
      assert (Hslotnext :
        0 <= Znth (Znth processed queue 0) head_data 0 < Zlength next_data)
        by (rewrite Hnext_len; exact Hhead_bounds).
      split; [exact Hvhead |]. split; [exact Hslotnext |].
      rewrite (Znth_indep head_data (Znth processed queue 0) (-1) 0)
        by exact Hvhead.
      unfold clos_refl_trans. sets_unfold.
      exists 0%nat. simpl. sets_unfold. reflexivity.
  }
  assert (Hto_bound :
    Znth (Znth processed queue 0) head_data 0 <> -1 ->
    0 <= Znth (Znth (Znth processed queue 0) head_data 0) to_data 0 < n).
  {
    intros Hnotminus.
    specialize (Hheads (Znth processed queue 0) Hvertex).
    rewrite (Znth_indep head_data (Znth processed queue 0) (-1) 0)
      in Hheads by (rewrite Hhead_len; exact Hvertex).
    destruct Hheads as [Hminus | Hhead_bounds]; [contradiction |].
    exact (proj1 (Hslots _ Hhead_bounds)).
  }
  assert (Hfrontier : BFSFrontierState n edges source
    (Znth processed queue 0) distances).
  {
    unfold GraphPre in Hgraph_old.
    destruct Hgraph_old as [_ [Hfrontier_complete _]].
    eapply Hfrontier_complete; eauto.
  }
  assert (Hscan : AdjacencyScanState head_data to_data next_data
    (Znth processed queue 0)
    (Znth (Znth processed queue 0) head_data 0) queue).
  {
    intros slot Hslot. left.
    unfold AdjacencySlot in Hslot.
    destruct Hslot as [_ [_ Hreach]].
    rewrite (Znth_indep head_data (Znth processed queue 0) (-1) 0)
      in Hreach by (rewrite Hhead_len; exact Hvertex).
    exact Hreach.
  }
  assert (Hend :
    Znth (Znth processed queue 0) head_data 0 = -1 ->
    forall neighbor,
      (In (Znth processed queue 0 + 1, neighbor + 1) edges \/
       In (neighbor + 1, Znth processed queue 0 + 1) edges) ->
      In neighbor queue).
  {
    intros Hminus neighbor Hedge.
    destruct (tree_edge_bounds__bfs_queue_entry n edges
      (Znth processed queue 0) neighbor Htree Hedge)
      as [_ Hneighbor].
    apply (proj2 (Hmembership neighbor Hneighbor)).
    destruct (Hedge_slots (Znth processed queue 0) neighbor
      Hvertex Hneighbor) as [Hto_slot _].
    destruct (Hto_slot Hedge) as [slot [Hslot Hto]].
    exfalso.
    unfold AdjacencySlot in Hslot.
    destruct Hslot as [_ [Hslot_bounds Hreach]].
    rewrite (Znth_indep head_data (Znth processed queue 0) (-1) 0)
      in Hreach by (rewrite Hhead_len; exact Hvertex).
    rewrite Hminus in Hreach.
    eapply adjacency_from_minus_one_impossible__bfs_queue_entry.
    - exact (proj1 Hslot_bounds).
    - exact Hreach.
  }
  assert (Hprocessed_new : 0 < processed + 1 <= Zlength queue) by lia.
  assert (Hqueue_new_shift : BFSQueueState n edges source
    (processed + 1 - 1) new_farthest queue parents distances).
  { replace (processed + 1 - 1) with processed by lia. exact Hqueue_new. }
  assert (Hvertex_eq :
    Znth processed queue 0 = Znth (processed + 1 - 1) queue 0).
  { replace (processed + 1 - 1) with processed by lia. reflexivity. }
  unfold BFSAdjState.
  exact (conj Hqueue_new_shift
    (conj Hprocessed_new
    (conj Hvertex_eq
    (conj Hcurrent
    (conj Hhead_range
    (conj Hhead_slot
    (conj Hto_bound
    (conj Hfrontier
    (conj Hscan Hend))))))))).
Qed.
Lemma unseen_head_implies_queue_not_full__bfs_queue_entry :
  forall n edges source processed farthest queue parents distances
    head_data to_data next_data,
    AdjacencyModel n edges head_data to_data next_data ->
    BFSQueueState n edges source processed farthest queue parents distances ->
    processed < Zlength queue ->
    Znth (Znth processed queue 0) head_data 0 <> -1 ->
    Znth (Znth (Znth (Znth processed queue 0) head_data 0)
      to_data 0) distances 0 < 0 ->
    Zlength queue < n.
Proof.
  intros n edges source processed farthest queue parents distances
    head_data to_data next_data Hmodel Hqueue Hprocessed Hhead Hnegative.
  unfold BFSQueueState in Hqueue.
  destruct Hqueue as
    [Hparents [Hdistances [Hprocessed_bounds [Hqueue_bounds
    [Hnodup [Hsource_head [Hsource_bounds [Hfar_bounds
    [Hparent_state [Hqueue_values [Hmembership _]]]]]]]]]]].
  assert (Hvertex : 0 <= Znth processed queue 0 < n).
  { exact (proj1 (Hqueue_values processed ltac:(lia))). }
  unfold AdjacencyModel in Hmodel.
  destruct Hmodel as
    [Hhead_len [Hto_len [Hnext_len [Hedges_len [Hheads [Hslots _]]]]]].
  specialize (Hheads (Znth processed queue 0) Hvertex).
  rewrite (Znth_indep head_data (Znth processed queue 0) (-1) 0)
    in Hheads by (rewrite Hhead_len; exact Hvertex).
  destruct Hheads as [Hminus | Hhead_bounds]; [contradiction |].
  pose proof (proj1 (Hslots _ Hhead_bounds)) as Hneighbor.
  destruct Hqueue_bounds as [Hqueue_pos Hqueue_le].
  assert (Hneq : Zlength queue <> n).
  {
    intro Heq.
    assert (Hin : In
      (Znth (Znth (Znth processed queue 0) head_data 0) to_data 0) queue).
    {
      eapply (bounded_nodup_full__bfs_queue_entry n queue).
      - lia.
      - exact Heq.
      - exact Hnodup.
      - intros i Hi. exact (proj1 (Hqueue_values i Hi)).
      - exact Hneighbor.
    }
    apply (proj1 (Hmembership _ Hneighbor)) in Hin.
    rewrite (Znth_indep distances
      (Znth (Znth (Znth processed queue 0) head_data 0) to_data 0)
      (-1) 0) in Hin by (rewrite Hdistances; lia).
    lia.
  }
  lia.
Qed.
Lemma adjacency_head_facts__bfs_queue_entry :
  forall n edges head_data to_data next_data vertex,
    AdjacencyModel n edges head_data to_data next_data ->
    0 <= vertex < n ->
    -1 <= Znth vertex head_data 0 < 2 * n - 2 /\
    (Znth vertex head_data 0 <> -1 ->
      (0 <= Znth (Znth vertex head_data 0) to_data 0 < n) /\
      (-1 <= Znth (Znth vertex head_data 0) next_data 0 <
        2 * n - 2)).
Proof.
  intros n edges head_data to_data next_data vertex Hmodel Hvertex.
  unfold AdjacencyModel in Hmodel.
  destruct Hmodel as
    [Hhead_len [Hto_len [Hnext_len [Hedges_len [Hheads [Hslots _]]]]]].
  specialize (Hheads vertex Hvertex).
  rewrite (Znth_indep head_data vertex (-1) 0) in Hheads
    by (rewrite Hhead_len; exact Hvertex).
  destruct Hheads as [Hminus | Hhead_bounds].
  - split; [lia | intros; contradiction].
  - split; [lia |].
    intros Hnotminus.
    specialize (Hslots (Znth vertex head_data 0) Hhead_bounds).
    destruct Hslots as [Hto Hnext].
    split; [exact Hto |].
    rewrite (Znth_indep next_data (Znth vertex head_data 0) (-1) 0)
      in Hnext by (rewrite Hnext_len; exact Hhead_bounds).
    destruct Hnext; lia.
Qed.
Lemma NoDup_Z_bounded_length__bfs_neighbor_step : forall xs n,
  0 <= n ->
  NoDup xs ->
  (forall x, In x xs -> 0 <= x < n) ->
  Zlength xs <= n.
Proof.
  intros xs n Hn Hnd Hbounds.
  assert (Hincl : incl xs (map Z.of_nat (seq 0 (Z.to_nat n)))).
  { intros x Hx.
    specialize (Hbounds x Hx).
    apply in_map_iff. exists (Z.to_nat x). split.
    - lia.
    - apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite length_map, length_seq in Hlen.
  rewrite Z2Nat.id in Hlen by exact Hn.
  rewrite <- Zlength_correct in Hlen.
  exact Hlen.
Qed.
Lemma In_Znth_index__bfs_neighbor_step : forall (xs : list Z) x d,
  In x xs ->
  exists i, 0 <= i < Zlength xs /\ Znth i xs d = x.
Proof.
  intros xs x d Hin.
  apply in_split in Hin.
  destruct Hin as [left [right ->]].
  exists (Zlength left). split.
  - rewrite Zlength_app, Zlength_cons.
    pose proof (Zlength_nonneg left). pose proof (Zlength_nonneg right). lia.
  - rewrite app_Znth2 by lia.
    replace (Zlength left - Zlength left) with 0 by lia.
    reflexivity.
Qed.
Lemma Zlength_replace_Znth__bfs_neighbor_step : forall {A : Type}
    (xs : list A) i (x : A),
  Zlength (replace_Znth i x xs) = Zlength xs.
Proof.
  intros A xs. induction xs as [|a xs IH]; intros i x; simpl; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat i) as [|k].
  - simpl. repeat rewrite Zlength_cons. lia.
  - simpl. repeat rewrite Zlength_cons.
    specialize (IH (Z.of_nat k) x).
    replace (Z.to_nat (Z.of_nat k)) with k in IH by lia.
    lia.
Qed.
Lemma GraphDistance_nontrivial_positive__bfs_neighbor_step :
  forall edges start finish distance,
  GraphDistance edges start finish distance ->
  start <> finish ->
  1 <= distance.
Proof.
  intros edges start finish distance
    [path [[Hpath Hnodup] [Hdistance Hminimal]]] Hneq.
  destruct path as [|a path].
  - exfalso. eapply valid_vpath_not_nil; eauto.
  - destruct path as [|b path].
    + pose proof (valid_vpath_empty_inv _ _ _ _ Hpath) as [Hstart Hfinish].
      congruence.
    + repeat rewrite Zlength_cons in Hdistance.
      pose proof (Zlength_nonneg path). lia.
Qed.
Lemma bfs_queue_enqueue__bfs_neighbor_step :
  forall n edges source processed farthest queue parents distances vertex neighbor,
  BFSQueueState n edges source (processed - 1) farthest queue parents distances ->
  0 < processed <= Zlength queue ->
  Zlength queue < n ->
  0 <= vertex < n ->
  In vertex queue ->
  0 <= neighbor < n ->
  ~ In neighbor queue ->
  (In (vertex + 1, neighbor + 1) edges \/
   In (neighbor + 1, vertex + 1) edges) ->
  GraphDistance edges (source + 1) (neighbor + 1)
    (Znth vertex distances 0 + 1) ->
  BFSQueueState n edges source (processed - 1) farthest
    (queue ++ [neighbor])
    (replace_Znth neighbor vertex parents)
    (replace_Znth neighbor (Znth vertex distances 0 + 1) distances).
Proof.
  intros n edges source processed farthest queue parents distances vertex neighbor
    Hold Hprocessed Hroom Hvertex Hin_vertex Hneighbor Hmissing Hedge Hneighbor_graph.
  unfold BFSQueueState in Hold |- *.
  destruct Hold as
    [Hparents_len [Hdist_len [Hold_processed [Hqueue_len [Hnodup
     [Hsource_head [Hsource_bounds [Hfar_bounds [Hparent
     [Hentries [Hmembership [Hprocessed_far [Hprocessed_neighbors Hgraph]]]]]]]]]]]]].
  assert (Hvertex_distance : 0 <= Znth vertex distances (-1)).
  { apply (proj1 (Hmembership vertex Hvertex)). exact Hin_vertex. }
  assert (Hvertex_default : Znth vertex distances (-1) = Znth vertex distances 0).
  { apply Znth_indep. rewrite Hdist_len. exact Hvertex. }
  assert (Hneighbor_source : neighbor <> source).
  { intros ->. apply Hmissing.
    apply (proj2 (Hmembership source Hsource_bounds)).
    specialize (Hentries 0 ltac:(lia)).
    rewrite Hsource_head in Hentries. tauto. }
  assert (Hneighbor_vertex : neighbor <> vertex).
  { intros ->. contradiction. }
  split.
  - rewrite Zlength_replace_Znth__bfs_neighbor_step. exact Hparents_len.
  - split.
    + rewrite Zlength_replace_Znth__bfs_neighbor_step. exact Hdist_len.
    + split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      * split.
        -- rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
        -- split.
           ++ apply NoDup_app. repeat split.
              ** exact Hnodup.
              ** constructor; [simpl; tauto | constructor].
              ** intros x Hx Hxn. simpl in Hxn.
                 destruct Hxn as [-> | []]. contradiction.
           ++ split.
              ** rewrite app_Znth1; [exact Hsource_head |].
                 pose proof (proj1 Hqueue_len). lia.
              ** split; [exact Hsource_bounds |].
                 split; [exact Hfar_bounds |].
                 split.
                 { unfold BFSParentState in Hparent |- *.
                     destruct Hparent as [Hsource_parent Hparent].
                     split.
                     + rewrite Znth_replace_Znth_Diff by
                         (try rewrite Hparents_len; lia).
                       exact Hsource_parent.
                     + intros x Hx Hxsource Hxdisc.
                       destruct (Z.eq_dec x neighbor) as [-> | Hxneighbor].
                       * repeat rewrite Znth_replace_Znth_Same by
                           (rewrite ?Zlength_replace_Znth__bfs_neighbor_step; lia).
                         split; [exact Hvertex |]. split; [destruct Hedge; tauto |].
                         rewrite Znth_replace_Znth_Diff by
                           (rewrite ?Zlength_replace_Znth__bfs_neighbor_step; lia).
                         lia.
                       * rewrite Znth_replace_Znth_Diff in Hxdisc by
                           (rewrite ?Zlength_replace_Znth__bfs_neighbor_step; lia).
                         specialize (Hparent x Hx Hxsource Hxdisc).
                         destruct Hparent as [Hp [Hedge_x Hdist_x]].
                         rewrite Znth_replace_Znth_Diff by
                           (rewrite ?Zlength_replace_Znth__bfs_neighbor_step; lia).
                         split; [exact Hp |]. split; [exact Hedge_x |].
                         rewrite Znth_replace_Znth_Diff by
                           (rewrite ?Zlength_replace_Znth__bfs_neighbor_step; lia).
                         destruct (Z.eq_dec (Znth x parents (-1)) neighbor)
                           as [Heq | Hneq].
                         { subst neighbor. exfalso. apply Hmissing.
                           apply (proj2 (Hmembership (Znth x parents (-1)) Hp)).
                           assert (Hxpositive : 1 <= Znth x distances (-1)).
                           { eapply GraphDistance_nontrivial_positive__bfs_neighbor_step.
                             - apply Hgraph; assumption.
                             - lia. }
                           lia. }
                         rewrite Znth_replace_Znth_Diff by
                           (rewrite ?Zlength_replace_Znth__bfs_neighbor_step; lia).
                         exact Hdist_x. }
                 { split.
                     + intros q Hq.
                       rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
                       destruct (Z_lt_ge_dec q (Zlength queue)) as [Hlt | Hge].
                       * rewrite app_Znth1 by lia.
                         destruct (Hentries q ltac:(lia)) as [Hqb Hqd].
                         split; [exact Hqb |].
                         assert (Hqneq : Znth q queue 0 <> neighbor).
                         { intros Heq. apply Hmissing. rewrite <- Heq.
                           apply Znth_In_Zlength. lia. }
                         rewrite Znth_replace_Znth_Diff by
                           (try rewrite Hdist_len; lia).
                         exact Hqd.
                       * assert (q = Zlength queue) by lia. subst q.
                         rewrite app_Znth2 by lia. replace (Zlength queue - Zlength queue) with 0 by lia.
                         simpl. split; [exact Hneighbor |].
                         rewrite Znth_replace_Znth_Same by (rewrite Hdist_len; lia).
                         rewrite <- Hvertex_default. lia.
                     + split.
                       * intros x Hx. split; intros Hxin.
                         -- apply in_app_iff in Hxin. destruct Hxin as [Hxin | Hxin].
                            ++ destruct (Z.eq_dec x neighbor) as [-> | Hneq].
                               ** contradiction.
                               ** rewrite Znth_replace_Znth_Diff by
                                    (try rewrite Hdist_len; lia).
                                  apply (proj1 (Hmembership x Hx)); exact Hxin.
                            ++ simpl in Hxin. destruct Hxin as [-> | []].
                               rewrite Znth_replace_Znth_Same by (try rewrite Hdist_len; lia).
                               rewrite <- Hvertex_default. lia.
                         -- apply in_app_iff.
                            destruct (Z.eq_dec x neighbor) as [-> | Hneq].
                            ++ right. simpl. auto.
                            ++ left. apply (proj2 (Hmembership x Hx)).
                               rewrite Znth_replace_Znth_Diff in Hxin by
                                 (try rewrite Hdist_len; lia).
                               exact Hxin.
                       * split.
                         -- intros q Hq.
                            assert (Hq_old : 0 <= q < Zlength queue) by
                              (destruct Hold_processed; lia).
                            assert (Hq_neighbor : Znth q queue 0 <> neighbor).
                            { intros Heq. apply Hmissing. rewrite <- Heq.
                              apply Znth_In_Zlength. exact Hq_old. }
                            assert (Hneighbor_negative :
                                Znth neighbor distances (-1) < 0).
                            { apply Z.lt_nge. intros Hge. apply Hmissing.
                              apply (proj2 (Hmembership neighbor Hneighbor)). exact Hge. }
                            assert (Hfar_neighbor : farthest <> neighbor).
                            { intros Heq. subst farthest.
                              pose proof (Hprocessed_far q Hq) as Hle.
                              destruct (Hentries q Hq_old) as [_ Hnonneg]. lia. }
                            rewrite app_Znth1 by
                              exact Hq_old.
                            rewrite Znth_replace_Znth_Diff;
                              [|rewrite Hdist_len; exact Hneighbor
                               |rewrite Hdist_len; exact (proj1 (Hentries q Hq_old))
                               |congruence].
                            rewrite Znth_replace_Znth_Diff;
                              [|rewrite Hdist_len; exact Hneighbor
                               |rewrite Hdist_len; exact Hfar_bounds
                               |congruence].
                            apply Hprocessed_far. exact Hq.
                         -- split.
                            ++ intros q x Hq Hedge_q.
                               apply in_app_iff. left.
                               rewrite app_Znth1 in Hedge_q by
                                 (destruct Hold_processed; lia).
                               eapply Hprocessed_neighbors; eauto.
                            ++ intros x Hx Hxdisc.
                               destruct (Z.eq_dec x neighbor) as [-> | Hneq].
                               ** rewrite Znth_replace_Znth_Same by
                                    (rewrite Hdist_len; exact Hneighbor).
                                  exact Hneighbor_graph.
                                  ** rewrite Znth_replace_Znth_Diff in Hxdisc by
                                    (try rewrite Hdist_len; lia).
                                  rewrite Znth_replace_Znth_Diff by
                                    (try rewrite Hdist_len; lia).
                                  apply Hgraph; assumption. }
Qed.
Lemma NoDup_Z_bounded_missing_length__bfs_neighbor_step : forall xs n x,
  NoDup xs ->
  (forall y, In y xs -> 0 <= y < n) ->
  0 <= x < n ->
  ~ In x xs ->
  Zlength xs < n.
Proof.
  intros xs n x Hnd Hbounds Hx Hnot.
  assert (Hnd' : NoDup (xs ++ [x])).
  { apply NoDup_app. repeat split.
    - exact Hnd.
    - constructor; [simpl; tauto | constructor].
    - intros a Ha Hax. simpl in Hax. destruct Hax as [-> | []]. contradiction. }
  assert (Hbounds' : forall y, In y (xs ++ [x]) -> 0 <= y < n).
  { intros y Hy. apply in_app_iff in Hy. destruct Hy as [Hy | Hy].
    - apply Hbounds; exact Hy.
    - simpl in Hy. destruct Hy as [-> | []]. exact Hx. }
  assert (Hn : 0 <= n) by lia.
  pose proof (NoDup_Z_bounded_length__bfs_neighbor_step (xs ++ [x]) n Hn Hnd' Hbounds') as Hlen.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen.
  lia.
Qed.
Lemma AdjacencyNext_functional__bfs_neighbor_step : forall next_data x y z,
  AdjacencyNext next_data x y ->
  AdjacencyNext next_data x z ->
  y = z.
Proof.
  intros next_data x y z [_ Hy] [_ Hz]. congruence.
Qed.
Lemma adjacency_path_advance__bfs_neighbor_step : forall next_data cursor next slot,
  AdjacencyNext next_data cursor next ->
  clos_refl_trans (AdjacencyNext next_data) cursor slot ->
  cursor = slot \/ clos_refl_trans (AdjacencyNext next_data) next slot.
Proof.
  intros next_data cursor next slot Hnext Hpath.
  unfold clos_refl_trans in Hpath.
  destruct Hpath as [steps Hpath].
  destruct steps as [|steps].
  - simpl in Hpath. sets_unfold in Hpath. left. exact Hpath.
  - simpl in Hpath. sets_unfold in Hpath.
    destruct Hpath as [mid [Hfirst Htail]].
    right. unfold clos_refl_trans. exists steps.
    destruct Hnext as [_ Hnext]. destruct Hfirst as [_ Hfirst].
    congruence.
Qed.
Lemma adjacency_scan_advance__bfs_neighbor_step :
  forall head_data to_data next_data vertex cursor next queue,
  AdjacencyScanState head_data to_data next_data vertex cursor queue ->
  AdjacencyNext next_data cursor next ->
  In (Znth cursor to_data 0) queue ->
  AdjacencyScanState head_data to_data next_data vertex next queue.
Proof.
  intros head_data to_data next_data vertex cursor next queue Hscan Hnext Hin.
  intros slot Hslot.
  specialize (Hscan slot Hslot).
  destruct Hscan as [Hpath | Hdone]; [|right; exact Hdone].
  destruct (adjacency_path_advance__bfs_neighbor_step _ _ _ _ Hnext Hpath)
    as [-> | Htail].
  - right. exact Hin.
  - left. exact Htail.
Qed.
Lemma adjacency_slot_next__bfs_neighbor_step :
  forall head_data next_data vertex cursor next,
  AdjacencySlot head_data next_data vertex cursor ->
  AdjacencyNext next_data cursor next ->
  0 <= next < Zlength next_data ->
  AdjacencySlot head_data next_data vertex next.
Proof.
  intros head_data next_data vertex cursor next
    [Hvertex [Hcursor Hpath]] Hstep Hnext.
  unfold AdjacencySlot. split; [exact Hvertex |].
  split; [exact Hnext |].
  pose proof (rt_trans_n1 (AdjacencyNext next_data)) as Htrans.
  sets_unfold in Htrans. apply Htrans.
  exists cursor. split; assumption.
Qed.
Lemma no_adjacency_path_from_minus_one__bfs_neighbor_step : forall next_data slot,
  0 <= slot ->
  ~ clos_refl_trans (AdjacencyNext next_data) (-1) slot.
Proof.
  intros next_data slot Hslot Hpath.
  unfold clos_refl_trans in Hpath.
  destruct Hpath as [steps Hpath].
  destruct steps as [|steps].
  - simpl in Hpath. sets_unfold in Hpath. lia.
  - simpl in Hpath. sets_unfold in Hpath.
    destruct Hpath as [mid [Hfirst Htail]].
    unfold AdjacencyNext in Hfirst. lia.
Qed.
Lemma adjacency_scan_finished__bfs_neighbor_step :
  forall n edges head_data to_data next_data vertex queue,
  TreeInput n edges ->
  AdjacencyModel n edges head_data to_data next_data ->
  0 <= vertex < n ->
  AdjacencyScanState head_data to_data next_data vertex (-1) queue ->
  forall neighbor,
    (In (vertex + 1, neighbor + 1) edges \/
     In (neighbor + 1, vertex + 1) edges) ->
    In neighbor queue.
Proof.
  intros n edges head_data to_data next_data vertex queue Htree Hmodel Hvertex Hscan neighbor Hedge.
  destruct Htree as [Hn [Hedgelen [Hedge_bounds [Hfresh Hconnected]]]].
  rewrite Forall_forall in Hedge_bounds.
  assert (Hneighbor : 0 <= neighbor < n).
  { destruct Hedge as [Hedge | Hedge].
    - pose proof (Hedge_bounds _ Hedge) as Hb. simpl in Hb. lia.
    - pose proof (Hedge_bounds _ Hedge) as Hb. simpl in Hb. lia. }
  destruct Hmodel as
    [Hhead [Hto [Hnext [Hedges [Hheads [Hslots [Hedge_slots Hunique]]]]]]].
  destruct (proj1 (Hedge_slots vertex neighbor Hvertex Hneighbor) Hedge)
    as [slot [Hslot Hto_slot]].
  specialize (Hscan slot Hslot).
  destruct Hscan as [Hpath | Hin]; [|rewrite Hto_slot in Hin; exact Hin].
  exfalso.
  eapply no_adjacency_path_from_minus_one__bfs_neighbor_step; [|exact Hpath].
  destruct Hslot as [_ [Hslot _]]. lia.
Qed.
Lemma bfs_adj_existing_advance__bfs_neighbor_step :
  forall n edges source processed farthest queue parents distances
         head_data to_data next_data vertex cursor,
  TreeInput n edges ->
  AdjacencyModel n edges head_data to_data next_data ->
  BFSAdjState n edges source processed farthest queue parents distances
    head_data to_data next_data vertex cursor ->
  cursor <> -1 ->
  0 <= Znth (Znth cursor to_data 0) distances 0 ->
  BFSAdjState n edges source processed farthest queue parents distances
    head_data to_data next_data vertex (Znth cursor next_data 0).
Proof.
  intros n edges source processed farthest queue parents distances
    head_data to_data next_data vertex cursor Htree Hmodel Hstate Hcursor Hdiscovered.
  unfold BFSAdjState in Hstate |- *.
  destruct Hstate as
    [Hbqs [Hprocessed [Hvertex [Hfar [Hcursor_bounds
     [Hcursor_slot [Htarget [Hfrontier [Hscan Hcomplete]]]]]]]]].
  pose proof Hmodel as Hmodel_full.
  destruct Hmodel as
    [Hheadlen [Htolen [Hnextlen [Hedgelen [Hhead_info
     [Hslot_info [Hedge_slot Hslot_unique]]]]]]].
  assert (Hcursor_nonneg : 0 <= cursor) by lia.
  assert (Hnext_default :
      Znth cursor next_data (-1) = Znth cursor next_data 0).
  { apply Znth_indep. rewrite Hnextlen. lia. }
  assert (Hstep : AdjacencyNext next_data cursor (Znth cursor next_data 0)).
  { unfold AdjacencyNext. split; [rewrite Hnextlen; lia |].
    symmetry. exact Hnext_default. }
  assert (Hcurrent_slot : AdjacencySlot head_data next_data vertex cursor).
  { destruct Hcursor_slot as [Hbad | Hslot]; [contradiction | exact Hslot]. }
  assert (Hcurrent_in : In (Znth cursor to_data 0) queue).
  { pose proof Hbqs as Hcopy.
    unfold BFSQueueState in Hcopy.
    destruct Hcopy as
      [_ [Hdistlen [_ [_ [_ [_ [_ [_ [_ [_ [Hmembership _]]]]]]]]]]].
    apply (proj2 (Hmembership (Znth cursor to_data 0) (Htarget Hcursor))).
    assert (Znth (Znth cursor to_data 0) distances (-1) =
            Znth (Znth cursor to_data 0) distances 0).
    { apply Znth_indep. rewrite Hdistlen. apply Htarget. exact Hcursor. }
    lia. }
  assert (Hvertex_bounds : 0 <= vertex < n).
  { pose proof Hbqs as Hcopy.
    unfold BFSQueueState in Hcopy.
    destruct Hcopy as
      [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hentries _]]]]]]]]]].
    specialize (Hentries (processed - 1) ltac:(lia)).
    rewrite <- Hvertex in Hentries. tauto. }
  assert (Hfar_bounds : 0 <= farthest < n).
  { pose proof Hbqs as Hcopy. unfold BFSQueueState in Hcopy.
    destruct Hcopy as [_ [_ [_ [_ [_ [_ [_ [Hfar_bounds _]]]]]]]].
    exact Hfar_bounds. }
  assert (Hscan' :
      AdjacencyScanState head_data to_data next_data vertex
        (Znth cursor next_data 0) queue).
  { eapply adjacency_scan_advance__bfs_neighbor_step; eauto. }
  pose proof (Hslot_info cursor) as Hcursor_info.
  specialize (Hcursor_info ltac:(lia)).
  destruct Hcursor_info as [Hcurrent_target Hnext_cases].
  rewrite Hnext_default in Hnext_cases.
  assert (Hnext_bounds : -1 <= Znth cursor next_data 0 < 2 * n - 2).
  { destruct Hnext_cases as [-> | Hnext_cases]; lia. }
  split; [exact Hbqs |].
  split; [exact Hprocessed |].
  split; [exact Hvertex |].
  split; [exact Hfar |].
  split; [exact Hnext_bounds |].
  split.
  - destruct Hnext_cases as [Hminus | Hinside].
    + left. exact Hminus.
    + right. eapply adjacency_slot_next__bfs_neighbor_step; eauto.
      rewrite Hnextlen. lia.
  - split.
    + intros Hnotminus.
      apply Hslot_info. lia.
    + split; [exact Hfrontier |].
      split; [exact Hscan' |].
      intros Hminus neighbor Hedge.
      rewrite Hminus in Hscan'.
      eapply adjacency_scan_finished__bfs_neighbor_step;
        [exact Htree | exact Hmodel_full | exact Hvertex_bounds |
         exact Hscan' | exact Hedge].
Qed.
Lemma bfs_adj_close__bfs_neighbor_step :
  forall n edges source processed farthest queue parents distances
         head_data to_data next_data vertex,
  BFSAdjState n edges source processed farthest queue parents distances
    head_data to_data next_data vertex (-1) ->
  BFSQueueState n edges source processed farthest queue parents distances.
Proof.
  intros n edges source processed farthest queue parents distances
    head_data to_data next_data vertex Hstate.
  unfold BFSAdjState in Hstate.
  destruct Hstate as
    [Hold [Hprocessed [Hvertex [Hcurrent_far [Hcursor_bounds
     [Hcursor_slot [Htarget [Hfrontier [Hscan Hcomplete]]]]]]]]].
  unfold BFSQueueState in Hold |- *.
  destruct Hold as
    [Hparents_len [Hdist_len [Hold_processed [Hqueue_len [Hnodup
     [Hsource_head [Hsource_bounds [Hfar_bounds [Hparent
     [Hentries [Hmembership [Hold_far [Hold_neighbors Hgraph]]]]]]]]]]]]].
  split; [exact Hparents_len |].
  split; [exact Hdist_len |].
  split; [lia |].
  split; [exact Hqueue_len |].
  split; [exact Hnodup |].
  split; [exact Hsource_head |].
  split; [exact Hsource_bounds |].
  split; [exact Hfar_bounds |].
  split; [exact Hparent |].
  split; [exact Hentries |].
  split; [exact Hmembership |].
  split.
  - intros q Hq.
    destruct (Z_lt_ge_dec q (processed - 1)) as [Hlt | Hge].
    + apply Hold_far. lia.
    + assert (q = processed - 1) by lia. subst q.
      rewrite <- Hvertex. exact Hcurrent_far.
  - split.
    + intros q neighbor Hq Hedge.
      destruct (Z_lt_ge_dec q (processed - 1)) as [Hlt | Hge].
      * eapply Hold_neighbors; eauto. lia.
      * assert (q = processed - 1) by lia. subst q.
        rewrite <- Hvertex in Hedge.
        apply (Hcomplete eq_refl neighbor Hedge).
    + exact Hgraph.
Qed.
Lemma bfs_adj_undiscovered_advance__bfs_neighbor_step :
  forall n edges source processed farthest queue parents distances
         head_data to_data next_data vertex cursor,
  TreeInput n edges ->
  AdjacencyModel n edges head_data to_data next_data ->
  BFSAdjState n edges source processed farthest queue parents distances
    head_data to_data next_data vertex cursor ->
  cursor <> -1 ->
  Znth (Znth cursor to_data 0) distances 0 < 0 ->
  Zlength queue < n ->
  BFSAdjState n edges source processed farthest
    (queue ++ [Znth cursor to_data 0])
    (replace_Znth (Znth cursor to_data 0) vertex parents)
    (replace_Znth (Znth cursor to_data 0)
       (Znth vertex distances 0 + 1) distances)
    head_data to_data next_data vertex (Znth cursor next_data 0).
Proof.
  intros n edges source processed farthest queue parents distances
    head_data to_data next_data vertex cursor Htree Hmodel Hstate
    Hcursor Hnegative Hroom.
  pose proof Hstate as Hstate_copy.
  unfold BFSAdjState in Hstate.
  destruct Hstate as
    [Hbqs [Hprocessed [Hvertex [Hfar [Hcursor_bounds
     [Hcursor_slot [Htarget [Hfrontier [Hscan Hcomplete]]]]]]]]].
  pose proof Hmodel as Hmodel_copy.
  destruct Hmodel as
    [Hheadlen [Htolen [Hnextlen [Hedgelen [Hhead_info
     [Hslot_info [Hedge_slot Hslot_unique]]]]]]].
  assert (Hcursor_nonneg : 0 <= cursor) by lia.
  assert (Hneighbor : 0 <= Znth cursor to_data 0 < n) by
    (apply Htarget; exact Hcursor).
  assert (Hcurrent_slot : AdjacencySlot head_data next_data vertex cursor).
  { destruct Hcursor_slot as [Hbad | Hslot]; [contradiction | exact Hslot]. }
  assert (Hvertex_bounds : 0 <= vertex < n).
  { pose proof Hbqs as Hcopy. unfold BFSQueueState in Hcopy.
    destruct Hcopy as
      [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hentries _]]]]]]]]]].
    specialize (Hentries (processed - 1) ltac:(lia)).
    rewrite <- Hvertex in Hentries. tauto. }
  assert (Hfar_bounds_new : 0 <= farthest < n).
  { pose proof Hbqs as Hcopy. unfold BFSQueueState in Hcopy.
    destruct Hcopy as [_ [_ [_ [_ [_ [_ [_ [Hfb _]]]]]]]]. exact Hfb. }
  assert (Hedge :
      In (vertex + 1, Znth cursor to_data 0 + 1) edges \/
      In (Znth cursor to_data 0 + 1, vertex + 1) edges).
  { apply (proj2 (Hedge_slot vertex (Znth cursor to_data 0)
      Hvertex_bounds Hneighbor)).
    exists cursor. split; [exact Hcurrent_slot | reflexivity]. }
  assert (Hdistance_default :
      Znth (Znth cursor to_data 0) distances (-1) =
      Znth (Znth cursor to_data 0) distances 0).
  { apply Znth_indep. pose proof Hbqs as Hcopy. unfold BFSQueueState in Hcopy.
    destruct Hcopy as [_ [Hlen _]]. rewrite Hlen. exact Hneighbor. }
  assert (Hmissing : ~ In (Znth cursor to_data 0) queue).
  { pose proof Hbqs as Hcopy. unfold BFSQueueState in Hcopy.
    destruct Hcopy as
      [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hmembership _]]]]]]]]]]].
    intros Hin. apply (proj1 (Hmembership _ Hneighbor)) in Hin.
    rewrite Hdistance_default in Hin. lia. }
  assert (Hin_vertex : In vertex queue).
  { rewrite Hvertex. apply Znth_In_Zlength. lia. }
  assert (Hvertex_default : Znth vertex distances (-1) = Znth vertex distances 0).
  { apply Znth_indep. pose proof Hbqs as Hcopy. unfold BFSQueueState in Hcopy.
    destruct Hcopy as [_ [Hlen _]]. rewrite Hlen. exact Hvertex_bounds. }
  assert (Hneighbor_graph :
      GraphDistance edges (source + 1) (Znth cursor to_data 0 + 1)
        (Znth vertex distances 0 + 1)).
  { specialize (Hfrontier (Znth cursor to_data 0) Hneighbor Hedge).
    rewrite Hdistance_default in Hfrontier.
    specialize (Hfrontier Hnegative). rewrite Hvertex_default in Hfrontier.
    exact Hfrontier. }
  assert (Hbqs_new :
      BFSQueueState n edges source (processed - 1) farthest
        (queue ++ [Znth cursor to_data 0])
        (replace_Znth (Znth cursor to_data 0) vertex parents)
        (replace_Znth (Znth cursor to_data 0)
          (Znth vertex distances 0 + 1) distances)).
  { eapply bfs_queue_enqueue__bfs_neighbor_step; eauto. }
  assert (Hfrontier_new :
      BFSFrontierState n edges source vertex
        (replace_Znth (Znth cursor to_data 0)
          (Znth vertex distances 0 + 1) distances)).
  { intros x Hx Hedge_x Hxnegative.
    assert (Hxneighbor : x <> Znth cursor to_data 0).
    { intros ->.
      rewrite Znth_replace_Znth_Same in Hxnegative by
        (pose proof Hbqs as Hcopy; unfold BFSQueueState in Hcopy;
         destruct Hcopy as [_ [Hlen _]]; rewrite Hlen; exact Hneighbor).
      pose proof Hbqs as Hcopy. unfold BFSQueueState in Hcopy.
      destruct Hcopy as
        [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hmembership _]]]]]]]]]]].
      pose proof (proj1 (Hmembership vertex Hvertex_bounds) Hin_vertex).
      rewrite Hvertex_default in H. lia. }
    rewrite Znth_replace_Znth_Diff in Hxnegative by
      (pose proof Hbqs as Hcopy; unfold BFSQueueState in Hcopy;
       destruct Hcopy as [_ [Hlen _]]; try rewrite Hlen; try lia; congruence).
    rewrite Znth_replace_Znth_Diff by
      (pose proof Hbqs as Hcopy; unfold BFSQueueState in Hcopy;
       destruct Hcopy as [_ [Hlen _]]; try rewrite Hlen; try lia; congruence).
    eapply Hfrontier; eauto. }
  assert (Hscan_new :
      AdjacencyScanState head_data to_data next_data vertex cursor
        (queue ++ [Znth cursor to_data 0])).
  { intros slot Hslot. specialize (Hscan slot Hslot).
    destruct Hscan as [Hpath | Hin]; [left; exact Hpath |].
    right. apply in_app_iff. left. exact Hin. }
  assert (Hmid :
      BFSAdjState n edges source processed farthest
        (queue ++ [Znth cursor to_data 0])
        (replace_Znth (Znth cursor to_data 0) vertex parents)
        (replace_Znth (Znth cursor to_data 0)
          (Znth vertex distances 0 + 1) distances)
        head_data to_data next_data vertex cursor).
  { unfold BFSAdjState.
    split; [exact Hbqs_new |].
    split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia |].
    split.
    - rewrite app_Znth1; [exact Hvertex | lia].
    - split.
      + rewrite Znth_replace_Znth_Diff;
          [|pose proof Hbqs as Hcopy; unfold BFSQueueState in Hcopy;
             destruct Hcopy as [_ [Hlen _]]; rewrite Hlen; exact Hneighbor
           |pose proof Hbqs as Hcopy; unfold BFSQueueState in Hcopy;
             destruct Hcopy as [_ [Hlen _]]; rewrite Hlen; exact Hvertex_bounds
           |congruence].
      destruct (Z.eq_dec farthest (Znth cursor to_data 0)) as [Heq | Hneq].
      * subst farthest. rewrite Znth_replace_Znth_Same by
          (pose proof Hbqs as Hcopy; unfold BFSQueueState in Hcopy;
           destruct Hcopy as [_ [Hlen _]]; rewrite Hlen; exact Hneighbor).
        pose proof Hbqs as Hcopy. unfold BFSQueueState in Hcopy.
        destruct Hcopy as
          [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hmembership _]]]]]]]]]]].
        pose proof (proj1 (Hmembership vertex Hvertex_bounds) Hin_vertex).
        rewrite Hvertex_default in H. lia.
      * rewrite Znth_replace_Znth_Diff;
          [|pose proof Hbqs as Hcopy; unfold BFSQueueState in Hcopy;
             destruct Hcopy as [_ [Hlen _]]; rewrite Hlen; exact Hneighbor
           |pose proof Hbqs as Hcopy; unfold BFSQueueState in Hcopy;
             destruct Hcopy as [_ [Hlen _]]; rewrite Hlen; exact Hfar_bounds_new
           |congruence].
        exact Hfar.
      + split; [exact Hcursor_bounds |].
        split; [destruct Hcursor_slot; tauto |].
        split; [exact Htarget |].
        split; [exact Hfrontier_new |].
        split; [exact Hscan_new |].
        intros Hbad. contradiction.
  }
  eapply bfs_adj_existing_advance__bfs_neighbor_step;
    [exact Htree | exact Hmodel_copy | exact Hmid | exact Hcursor |].
  rewrite Znth_replace_Znth_Same by
    (pose proof Hbqs as Hcopy; unfold BFSQueueState in Hcopy;
     destruct Hcopy as [_ [Hlen _]]; rewrite Hlen; exact Hneighbor).
  pose proof Hbqs as Hcopy. unfold BFSQueueState in Hcopy.
  destruct Hcopy as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hmembership _]]]]]]]]]]].
  pose proof (proj1 (Hmembership vertex Hvertex_bounds) Hin_vertex).
  rewrite Hvertex_default in H. lia.
Qed.
Lemma bfs_queue_missing_length__bfs_neighbor_step :
  forall n edges source processed farthest queue parents distances x,
  BFSQueueState n edges source processed farthest queue parents distances ->
  0 <= x < n ->
  Znth x distances 0 < 0 ->
  Zlength queue < n.
Proof.
  intros n edges source processed farthest queue parents distances x
    Hstate Hx Hnegative.
  unfold BFSQueueState in Hstate.
  destruct Hstate as
    [_ [Hdistlen [_ [_ [Hnodup [_ [_ [_ [_ [Hentries
     [Hmembership _]]]]]]]]]]].
  assert (Hmissing : ~ In x queue).
  { intros Hin. apply (proj1 (Hmembership x Hx)) in Hin.
    assert (Znth x distances (-1) = Znth x distances 0).
    { apply Znth_indep. rewrite Hdistlen. exact Hx. }
    lia. }
  eapply NoDup_Z_bounded_missing_length__bfs_neighbor_step; eauto.
  intros y Hy.
  destruct (In_Znth_index__bfs_neighbor_step queue y 0 Hy)
    as [i [Hi Hiy]].
  specialize (Hentries i Hi). rewrite Hiy in Hentries. tauto.
Qed.
Lemma vertex_range_spec__bfs_final_result : forall n x,
  0 <= n ->
  (In x (map Z.of_nat (seq 0 (Z.to_nat n))) <-> 0 <= x < n).
Proof.
  intros n x Hn.
  split.
  - intros Hin. apply in_map_iff in Hin.
    destruct Hin as [i [<- Hi]]. apply in_seq in Hi. lia.
  - intros Hx. apply in_map_iff.
    exists (Z.to_nat x). split.
    + rewrite Z2Nat.id by lia. reflexivity.
    + apply in_seq. lia.
Qed.
Lemma vertex_range_nodup__bfs_final_result : forall n,
  NoDup (map Z.of_nat (seq 0 (Z.to_nat n))).
Proof.
  intros n.
  apply NoDup_map_NoDup_ForallPairs.
  - unfold ForallPairs. intros a b _ _ Heq.
    apply Nat2Z.inj in Heq. exact Heq.
  - apply seq_NoDup.
Qed.
Lemma vertex_range_Zlength__bfs_final_result : forall n,
  0 <= n -> Zlength (map Z.of_nat (seq 0 (Z.to_nat n))) = n.
Proof.
  intros n Hn.
  rewrite Zlength_correct, length_map, length_seq, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma In_has_Znth__bfs_final_result : forall (l : list Z) x,
  In x l -> exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros l x Hin.
  destruct (In_nth l x 0 Hin) as [i [Hi Heq]].
  exists (Z.of_nat i). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Heq.
Qed.
Lemma hedgehog_step_edge__bfs_final_result : forall edges u v,
  GraphLib.reachable.reachable_basic.step (HedgehogGraph edges) u v ->
  In (u, v) edges \/ In (v, u) edges.
Proof.
  intros edges u v [edge Hstep].
  simpl in Hstep. unfold zstep_aux in Hstep.
  tauto.
Qed.
Lemma hedgehog_vpath_forward_closed__bfs_final_result :
  forall edges queue u path v,
  valid_vpath (HedgehogGraph edges) u path v ->
  (forall x y,
      In (x - 1) queue ->
      (In (x, y) edges \/ In (y, x) edges) ->
      In (y - 1) queue) ->
  In (u - 1) queue ->
  In (v - 1) queue.
Proof.
  intros edges queue u path v Hpath Hclosed.
  pattern u, path, v. revert u path v Hpath.
  eapply valid_vpath_ind_1n.
  - intros x Hx. exact Hx.
  - intros x y p z Hstep Htail IH Hx.
    apply IH. eapply Hclosed; [exact Hx|].
    apply hedgehog_step_edge__bfs_final_result. exact Hstep.
Qed.
Lemma hedgehog_vpath_backward_closed__bfs_final_result :
  forall edges queue u path v,
  valid_vpath (HedgehogGraph edges) u path v ->
  (forall x y,
      In (x - 1) queue ->
      (In (x, y) edges \/ In (y, x) edges) ->
      In (y - 1) queue) ->
  In (v - 1) queue ->
  In (u - 1) queue.
Proof.
  intros edges queue u path v Hpath Hclosed.
  pattern u, path, v. revert u path v Hpath.
  eapply valid_vpath_ind_n1.
  - intros x Hx. exact Hx.
  - intros x p y z Hprefix IH Hstep Hz.
    apply IH. eapply Hclosed; [exact Hz|].
    pose proof (hedgehog_step_edge__bfs_final_result edges y z Hstep) as Hedge.
    tauto.
Qed.
Lemma bfs_queue_complete_result__bfs_final_result :
  forall n edges source processed farthest queue parents distances,
  GraphPre n edges ->
  BFSQueueState n edges source processed farthest queue parents distances ->
  Zlength queue <= processed ->
  Zlength queue = n /\
  BFSResult n edges source parents distances farthest.
Proof.
  intros n edges source processed farthest queue parents distances
    Hgraph Hqueue Hdone.
  unfold GraphPre in Hgraph.
  destruct Hgraph as [Htree [_ _]].
  unfold TreeInput in Htree.
  destruct Htree as [[Hnpos Hnmax]
    [Hedges [Hedge_bounds [Hfresh Hconnected]]]].
  unfold BFSQueueState in Hqueue.
  destruct Hqueue as
    (Hparents & Hdistances & Hprocessed & Hqlen & Hnodup & Hsource0 &
     Hsource_bounds & Hfar_bounds & Hparent_state & Hqueue_bounds &
     Hmembership & Hfar & Hneighbors & Hgraph_distance).
  assert (Hsource_in : In source queue).
  {
    unfold Znth in Hsource0.
    rewrite <- Hsource0.
    apply nth_In.
    destruct queue as [|a tl].
    - exfalso. rewrite Zlength_nil in Hqlen. lia.
    - apply Nat.lt_0_succ.
  }
  assert (Hedge_closed : forall x y,
      In (x - 1) queue ->
      (In (x, y) edges \/ In (y, x) edges) ->
      In (y - 1) queue).
  {
    intros x y Hxin Hedge.
    destruct (In_has_Znth__bfs_final_result queue (x - 1) Hxin)
      as [i [Hi Hix]].
    eapply Hneighbors with (q := i).
    - lia.
    - replace (Znth i queue 0 + 1) with x by lia.
      replace (y - 1 + 1) with y by lia.
      exact Hedge.
  }
  assert (Hroot_in : In 0 queue).
  {
    destruct (Hconnected (source + 1)) as [path [Hpath _]]; [lia|].
    replace source with (source + 1 - 1) in Hsource_in by lia.
    replace 0 with (1 - 1) by lia.
    eapply hedgehog_vpath_backward_closed__bfs_final_result;
      eauto.
  }
  assert (Hall : forall v, 0 <= v < n -> In v queue).
  {
    intros v Hv.
    destruct (Hconnected (v + 1)) as [path [Hpath _]]; [lia|].
    replace v with (v + 1 - 1) by lia.
    replace 0 with (1 - 1) in Hroot_in by lia.
    eapply hedgehog_vpath_forward_closed__bfs_final_result;
      eauto.
  }
  assert (Hnle : n <= Zlength queue).
  {
    assert (Hincl : incl (map Z.of_nat (seq 0 (Z.to_nat n))) queue).
    { intros x Hx. apply Hall.
      apply (proj1 (vertex_range_spec__bfs_final_result n x ltac:(lia))).
      exact Hx. }
    pose proof
      (NoDup_incl_length (vertex_range_nodup__bfs_final_result n) Hincl)
      as Hlen.
    apply Nat2Z.inj_le in Hlen.
    rewrite <- !Zlength_correct in Hlen.
    rewrite vertex_range_Zlength__bfs_final_result in Hlen by lia.
    lia.
  }
  assert (Hcomplete : Zlength queue = n) by lia.
  split; [exact Hcomplete|].
  unfold BFSResult, BFSData.
  split.
  - split; [exact Hparents|].
    split; [exact Hdistances|].
    split; [exact Hsource_bounds|].
    split; [exact Hparent_state|].
    intros v Hv.
    apply Hgraph_distance; [exact Hv|].
    apply (proj1 (Hmembership v Hv)). apply Hall. exact Hv.
  - split; [exact Hfar_bounds|].
    intros v Hv.
    destruct (In_has_Znth__bfs_final_result queue v (Hall v Hv))
      as [i [Hi Hiv]].
    specialize (Hfar i ltac:(lia)).
    rewrite Hiv in Hfar. exact Hfar.
Qed.
Lemma Zlength_replace_Znth__solver_build_step :
  forall (A : Type) (xs : list A) i v,
    Zlength (replace_Znth i v xs) = Zlength xs.
Proof.
  intros A xs i v. revert i.
  induction xs as [|x xs IH]; intros i; simpl; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat i) as [|m].
  - simpl. repeat rewrite Zlength_cons. lia.
  - simpl. repeat rewrite Zlength_cons.
    specialize (IH (Z.of_nat m)).
    replace (Z.to_nat (Z.of_nat m)) with m in IH by lia.
    rewrite IH. lia.
Qed.
Lemma Znth_app_left__solver_build_step :
  forall (A : Type) (xs ys : list A) i d,
    0 <= i < Zlength xs ->
    Znth i (xs ++ ys) d = Znth i xs d.
Proof.
  intros A xs. induction xs as [|x xs IH]; intros ys i d Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Znth_app_last__solver_build_step :
  forall (A : Type) (xs : list A) x d,
    Znth (Zlength xs) (xs ++ x :: nil) d = x.
Proof.
  intros A xs. induction xs as [|y xs IH]; intros x d.
  - reflexivity.
  - simpl. rewrite Zlength_cons.
    rewrite Znth_cons by (pose proof (Zlength_nonneg xs); lia).
    replace (Z.succ (Zlength xs) - 1) with (Zlength xs) by lia.
    exact (IH x d).
Qed.
Lemma Znth_replace_same__solver_build_step :
  forall (A : Type) (xs : list A) i v d,
    0 <= i < Zlength xs ->
    Znth i (replace_Znth i v xs) d = v.
Proof.
  intros A xs i v d Hi.
  apply Znth_replace_Znth_Same. exact Hi.
Qed.
Lemma Znth_replace_diff__solver_build_step :
  forall (A : Type) (xs : list A) i j v d,
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs -> i <> j ->
    Znth j (replace_Znth i v xs) d = Znth j xs d.
Proof.
  intros A xs i j v d Hi Hj Hneq.
  apply Znth_replace_Znth_Diff; assumption.
Qed.
Lemma adjacency_path_app_old__solver_build_step :
  forall next_data a b done start finish,
    Zlength next_data = 2 * done ->
    (forall slot, 0 <= slot < 2 * done ->
      Znth slot next_data (-1) = -1 \/
      0 <= Znth slot next_data (-1) < slot) ->
    (start = -1 \/ 0 <= start < 2 * done) ->
    clos_refl_trans
      (AdjacencyNext (next_data ++ a :: b :: nil)) start finish ->
    clos_refl_trans (AdjacencyNext next_data) start finish.
Proof.
  intros next_data a b done start finish Hlen Hslots Hstart Hpath.
  unfold clos_refl_trans in Hpath. unfold clos_refl_trans.
  sets_unfold in Hpath. sets_unfold.
  destruct Hpath as [steps Hsteps]. exists steps.
  revert start Hstart Hsteps.
  induction steps as [|steps IH]; intros start Hstart Hsteps.
  - simpl in Hsteps |- *. sets_unfold in Hsteps. sets_unfold. exact Hsteps.
  - simpl in Hsteps |- *. sets_unfold in Hsteps. sets_unfold.
    destruct Hsteps as [middle [Hstep Htail]].
    destruct Hstep as [Hfrom Hmiddle].
    assert (Hfrom_old : 0 <= start < 2 * done) by
      (destruct Hstart; subst; rewrite !Zlength_app, !Zlength_cons,
       Zlength_nil in Hfrom; lia).
    assert (Hstep_old : AdjacencyNext next_data start middle).
    { split; [rewrite Hlen; exact Hfrom_old |].
      rewrite Znth_app_left__solver_build_step in Hmiddle by
        (rewrite Hlen; exact Hfrom_old).
      exact Hmiddle. }
    assert (Hmiddle_old : middle = -1 \/ 0 <= middle < 2 * done).
    { specialize (Hslots start Hfrom_old).
      rewrite Znth_app_left__solver_build_step in Hmiddle by
        (rewrite Hlen; exact Hfrom_old).
      destruct Hslots; [left | right]; lia. }
    exists middle. split; [exact Hstep_old |].
    apply (IH middle Hmiddle_old Htail).
Qed.
Lemma adjacency_path_old_app__solver_build_step :
  forall next_data a b start finish,
    clos_refl_trans (AdjacencyNext next_data) start finish ->
    clos_refl_trans
      (AdjacencyNext (next_data ++ a :: b :: nil)) start finish.
Proof.
  intros next_data a b start finish Hpath.
  unfold clos_refl_trans in Hpath. unfold clos_refl_trans.
  sets_unfold in Hpath. sets_unfold.
  destruct Hpath as [steps Hsteps]. exists steps.
  revert start Hsteps.
  induction steps as [|steps IH]; intros start Hsteps.
  - simpl in Hsteps |- *. sets_unfold in Hsteps. sets_unfold. exact Hsteps.
  - simpl in Hsteps |- *. sets_unfold in Hsteps. sets_unfold.
    destruct Hsteps as [middle [Hstep Htail]].
    exists middle. split.
    + destruct Hstep as [Hfrom Hmiddle]. split.
      * repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
        rewrite Zlength_nil. lia.
      * rewrite Znth_app_left__solver_build_step by exact Hfrom.
        exact Hmiddle.
    + apply IH. exact Htail.
Qed.
Lemma adjacency_step_path__solver_build_step :
  forall next_data x y z,
    AdjacencyNext next_data x y ->
    clos_refl_trans (AdjacencyNext next_data) y z ->
    clos_refl_trans (AdjacencyNext next_data) x z.
Proof.
  intros next_data x y z Hxy Hyz.
  unfold clos_refl_trans in Hyz. unfold clos_refl_trans.
  sets_unfold in Hyz. sets_unfold.
  destruct Hyz as [steps Hsteps]. exists (S steps).
  simpl. sets_unfold. exists y. auto.
Qed.
Lemma adjacency_path_finish_bound__solver_build_step :
  forall next_data done start finish,
    (forall slot, 0 <= slot < 2 * done ->
      Znth slot next_data (-1) = -1 \/
      0 <= Znth slot next_data (-1) < slot) ->
    (start = -1 \/ 0 <= start < 2 * done) ->
    clos_refl_trans (AdjacencyNext next_data) start finish ->
    finish = -1 \/ 0 <= finish < 2 * done.
Proof.
  intros next_data done start finish Hslots Hstart Hpath.
  unfold clos_refl_trans in Hpath. sets_unfold in Hpath.
  destruct Hpath as [steps Hsteps]. revert start Hstart Hsteps.
  induction steps as [|steps IH]; intros start Hstart Hsteps.
  - simpl in Hsteps. sets_unfold in Hsteps. subst finish. exact Hstart.
  - simpl in Hsteps. sets_unfold in Hsteps.
    destruct Hsteps as [middle [Hstep Htail]].
    unfold AdjacencyNext in Hstep. destruct Hstep as [Hfrom Hmiddle].
    assert (Hfrom_old : 0 <= start < 2 * done) by
      (destruct Hstart; subst; lia).
    specialize (Hslots start Hfrom_old).
    assert (Hmiddle_old : middle = -1 \/ 0 <= middle < 2 * done) by
      (destruct Hslots; [left | right]; lia).
    apply (IH middle Hmiddle_old Htail).
Qed.
Lemma adjacency_slot_push_iff__solver_build_step :
  forall n done head_data next_data u v,
    Zlength head_data = n ->
    Zlength next_data = 2 * done ->
    (forall x, 0 <= x < n ->
      Znth x head_data (-1) = -1 \/
      0 <= Znth x head_data (-1) < 2 * done) ->
    (forall slot, 0 <= slot < 2 * done ->
      Znth slot next_data (-1) = -1 \/
      0 <= Znth slot next_data (-1) < slot) ->
    0 <= done ->
    0 <= u < n -> 0 <= v < n -> u <> v ->
    forall x slot,
      AdjacencySlot
        (replace_Znth v (2 * done + 1)
          (replace_Znth u (2 * done) head_data))
        (next_data ++ Znth u head_data (-1) ::
          Znth v (replace_Znth u (2 * done) head_data) (-1) :: nil)
        x slot <->
      AdjacencySlot head_data next_data x slot \/
      (x = u /\ slot = 2 * done) \/
      (x = v /\ slot = 2 * done + 1).
Proof.
  intros n done head_data next_data u v Hhead Hnext Hheads Hslots
    Hdone Hu Hv Huv x slot.
  set (head1 := replace_Znth u (2 * done) head_data).
  set (head2 := replace_Znth v (2 * done + 1) head1).
  set (next2 := next_data ++ Znth u head_data (-1) ::
    Znth v head1 (-1) :: nil).
  assert (Hhead1 : Zlength head1 = n).
  { unfold head1. rewrite Zlength_replace_Znth__solver_build_step.
    exact Hhead. }
  assert (Hhead2 : Zlength head2 = n).
  { unfold head2. rewrite Zlength_replace_Znth__solver_build_step.
    exact Hhead1. }
  assert (Hnext2 : Zlength next2 = 2 * done + 2).
  { unfold next2. repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
    rewrite Zlength_nil, Hnext. lia. }
  assert (Hhead1_v : Znth v head1 (-1) = Znth v head_data (-1)).
  { unfold head1. apply Znth_replace_diff__solver_build_step;
      rewrite ?Hhead; lia. }
  assert (Hhead2_u : Znth u head2 (-1) = 2 * done).
  { unfold head2, head1.
    rewrite Znth_replace_diff__solver_build_step by
      (rewrite ?Zlength_replace_Znth__solver_build_step, ?Hhead; lia).
    apply Znth_replace_same__solver_build_step. rewrite Hhead. lia. }
  assert (Hhead2_v : Znth v head2 (-1) = 2 * done + 1).
  { unfold head2. apply Znth_replace_same__solver_build_step.
    rewrite Hhead1. lia. }
  assert (Hhead2_other : forall y, 0 <= y < n -> y <> u -> y <> v ->
      Znth y head2 (-1) = Znth y head_data (-1)).
  { intros y Hy Hyu Hyv. unfold head2, head1.
    rewrite Znth_replace_diff__solver_build_step by
      (rewrite ?Zlength_replace_Znth__solver_build_step, ?Hhead; lia).
    apply Znth_replace_diff__solver_build_step; rewrite ?Hhead; lia. }
  assert (Hnext_u : AdjacencyNext next2 (2 * done) (Znth u head_data (-1))).
  { split; [rewrite Hnext2; lia |]. unfold next2.
    replace (Znth u head_data (-1) :: Znth v head1 (-1) :: nil)
      with ((Znth u head_data (-1) :: nil) ++ Znth v head1 (-1) :: nil)
      by reflexivity.
    rewrite app_assoc.
    rewrite Znth_app_left__solver_build_step by
      (repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
       rewrite Zlength_nil, Hnext; lia).
    replace (2 * done) with (Zlength next_data) by lia.
    symmetry. apply Znth_app_last__solver_build_step. }
  assert (Hnext_v : AdjacencyNext next2 (2 * done + 1) (Znth v head_data (-1))).
  { split; [rewrite Hnext2; lia |]. unfold next2.
    replace (Znth u head_data (-1) :: Znth v head1 (-1) :: nil)
      with ((Znth u head_data (-1) :: nil) ++ Znth v head1 (-1) :: nil)
      by reflexivity.
    rewrite app_assoc.
    rewrite <- Hhead1_v.
    replace (2 * done + 1) with
      (Zlength (next_data ++ Znth u head_data (-1) :: nil)).
    - symmetry. apply Znth_app_last__solver_build_step.
    - repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
      rewrite Zlength_nil, Hnext. lia. }
  change (AdjacencySlot head2 next2 x slot <->
    AdjacencySlot head_data next_data x slot \/
    (x = u /\ slot = 2 * done) \/
    (x = v /\ slot = 2 * done + 1)).
  split.
  - intros Hnew. unfold AdjacencySlot in Hnew.
    destruct Hnew as [Hx [Hslot Hpath]].
    assert (Hxn : 0 <= x < n) by (rewrite <- Hhead2; exact Hx).
    destruct (Z.eq_dec x u) as [Hxu | Hxu].
    + subst x. rewrite Hhead2_u in Hpath.
      unfold clos_refl_trans in Hpath; sets_unfold in Hpath.
      destruct Hpath as [steps Hsteps]. destruct steps as [|steps].
      * simpl in Hsteps. sets_unfold in Hsteps. subst slot.
        right; left; auto.
      * simpl in Hsteps. sets_unfold in Hsteps.
        destruct Hsteps as [middle [Hstep Htail]].
        assert (Hmiddle : middle = Znth u head_data (-1)).
        { unfold AdjacencyNext in Hstep, Hnext_u.
          destruct Hstep as [_ Hm]. destruct Hnext_u as [_ Hu_next].
          rewrite Hm, Hu_next. reflexivity. }
        subst middle.
        assert (Hold_head : Znth u head_data (-1) = -1 \/
                   0 <= Znth u head_data (-1) < 2 * done).
        { apply Hheads. exact Hu. }
        assert (Hreach_old : clos_refl_trans (AdjacencyNext next_data)
            (Znth u head_data (-1)) slot).
        { apply adjacency_path_app_old__solver_build_step with
              (a := Znth u head_data (-1)) (b := Znth v head1 (-1))
              (done := done); try assumption.
          unfold clos_refl_trans; sets_unfold. exists steps. exact Htail. }
        assert (Hfinish := adjacency_path_finish_bound__solver_build_step
          next_data done (Znth u head_data (-1)) slot Hslots Hold_head Hreach_old).
        left. unfold AdjacencySlot.
        split; [rewrite Hhead; exact Hu |]. split; [lia | exact Hreach_old].
    + destruct (Z.eq_dec x v) as [Hxv | Hxv].
      * subst x. rewrite Hhead2_v in Hpath.
        unfold clos_refl_trans in Hpath; sets_unfold in Hpath.
        destruct Hpath as [steps Hsteps]. destruct steps as [|steps].
        -- simpl in Hsteps. sets_unfold in Hsteps. subst slot.
           right; right; auto.
        -- simpl in Hsteps. sets_unfold in Hsteps.
           destruct Hsteps as [middle [Hstep Htail]].
           assert (Hmiddle : middle = Znth v head_data (-1)).
           { unfold AdjacencyNext in Hstep, Hnext_v.
             destruct Hstep as [_ Hm]. destruct Hnext_v as [_ Hv_next].
             rewrite Hm, Hv_next. reflexivity. }
           subst middle.
           assert (Hold_head : Znth v head_data (-1) = -1 \/
                     0 <= Znth v head_data (-1) < 2 * done).
           { apply Hheads. exact Hv. }
           assert (Hreach_old : clos_refl_trans (AdjacencyNext next_data)
               (Znth v head_data (-1)) slot).
           { apply adjacency_path_app_old__solver_build_step with
                 (a := Znth u head_data (-1)) (b := Znth v head1 (-1))
                 (done := done); try assumption.
             unfold clos_refl_trans; sets_unfold. exists steps. exact Htail. }
           assert (Hfinish := adjacency_path_finish_bound__solver_build_step
             next_data done (Znth v head_data (-1)) slot Hslots Hold_head Hreach_old).
           left. unfold AdjacencySlot.
           split; [rewrite Hhead; exact Hv |]. split; [lia | exact Hreach_old].
      * assert (Hold_head : Znth x head_data (-1) = -1 \/
                   0 <= Znth x head_data (-1) < 2 * done).
        { apply Hheads. exact Hxn. }
        rewrite Hhead2_other in Hpath by auto.
        assert (Hreach_old : clos_refl_trans (AdjacencyNext next_data)
            (Znth x head_data (-1)) slot).
        { apply adjacency_path_app_old__solver_build_step with
            (a := Znth u head_data (-1)) (b := Znth v head1 (-1))
            (done := done); try assumption. }
        assert (Hfinish := adjacency_path_finish_bound__solver_build_step
          next_data done (Znth x head_data (-1)) slot Hslots Hold_head Hreach_old).
        left. unfold AdjacencySlot.
        split; [rewrite Hhead; exact Hxn |]. split; [lia | exact Hreach_old].
  - intros [Hold | [[-> ->] | [-> ->]]].
    + unfold AdjacencySlot in Hold |- *.
      destruct Hold as [Hx [Hslot Hpath]].
      assert (Hxn : 0 <= x < n) by (rewrite <- Hhead; exact Hx).
      split; [rewrite Hhead2; exact Hxn |]. split; [rewrite Hnext2; lia |].
      destruct (Z.eq_dec x u) as [-> | Hxu].
      * rewrite Hhead2_u.
        apply adjacency_step_path__solver_build_step with
          (y := Znth u head_data (-1)); [exact Hnext_u |].
        apply adjacency_path_old_app__solver_build_step. exact Hpath.
      * destruct (Z.eq_dec x v) as [-> | Hxv].
        -- rewrite Hhead2_v.
           apply adjacency_step_path__solver_build_step with
             (y := Znth v head_data (-1)); [exact Hnext_v |].
           apply adjacency_path_old_app__solver_build_step. exact Hpath.
        -- rewrite Hhead2_other by auto.
           apply adjacency_path_old_app__solver_build_step. exact Hpath.
    + unfold AdjacencySlot. split; [rewrite Hhead2; exact Hu |].
      split; [rewrite Hnext2; lia |]. rewrite Hhead2_u.
      unfold clos_refl_trans; sets_unfold. exists 0%nat. simpl. sets_unfold. reflexivity.
    + unfold AdjacencySlot. split; [rewrite Hhead2; exact Hv |].
      split; [rewrite Hnext2; lia |]. rewrite Hhead2_v.
      unfold clos_refl_trans; sets_unfold. exists 0%nat. simpl. sets_unfold. reflexivity.
Qed.
Lemma firstn_succ_Znth__solver_build_step :
  forall (A : Type) (l : list A) i d,
    0 <= i < Zlength l ->
    firstn (Z.to_nat (i + 1)) l =
      firstn (Z.to_nat i) l ++ Znth i l d :: nil.
Proof.
  intros A l i d Hi.
  assert (Hsucc : Z.to_nat (i + 1) = S (Z.to_nat i)) by lia.
  rewrite Hsucc. unfold Znth.
  remember (Z.to_nat i) as m eqn:Hm.
  assert (Hnat : (m < length l)%nat).
  { subst m. apply (proj2 (Nat2Z.inj_lt _ _)).
    rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. lia. }
  clear Hsucc Hm i Hi. revert m Hnat.
  induction l as [|x l IH]; intros m Hnat.
  - simpl in Hnat. lia.
  - destruct m as [|m].
    + reflexivity.
    + simpl. f_equal. apply IH. simpl in Hnat. lia.
Qed.
Lemma sublist_prefix_succ__solver_build_step :
  forall (A : Type) (l : list A) i d,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l d :: nil.
Proof.
  intros A l i d Hi.
  unfold sublist. simpl.
  apply firstn_succ_Znth__solver_build_step. exact Hi.
Qed.
Lemma Znth_app_two_first__solver_build_step :
  forall (A : Type) (xs : list A) a b d,
    Znth (Zlength xs) (xs ++ a :: b :: nil) d = a.
Proof.
  intros A xs a b d.
  replace (a :: b :: nil) with ((a :: nil) ++ b :: nil) by reflexivity.
  rewrite app_assoc.
  rewrite Znth_app_left__solver_build_step.
  - apply Znth_app_last__solver_build_step.
  - repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
    rewrite Zlength_nil. pose proof (Zlength_nonneg xs). lia.
Qed.
Lemma Znth_app_two_second__solver_build_step :
  forall (A : Type) (xs : list A) a b d,
    Znth (Zlength xs + 1) (xs ++ a :: b :: nil) d = b.
Proof.
  intros A xs a b d.
  replace (a :: b :: nil) with ((a :: nil) ++ b :: nil) by reflexivity.
  rewrite app_assoc.
  replace (Zlength xs + 1) with (Zlength (xs ++ a :: nil)).
  - apply Znth_app_last__solver_build_step.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.
Lemma canonical_swap__solver_build_step :
  forall u v, CanonicalEdge (u, v) = CanonicalEdge (v, u).
Proof.
  intros u v. unfold CanonicalEdge. simpl.
  destruct (Z.leb_spec u v); destruct (Z.leb_spec v u);
    try reflexivity; f_equal; lia.
Qed.
Lemma adjacency_build_extend__solver_build_step :
  forall n edges i head_data to_data next_data u v d,
    0 <= i < Zlength edges ->
    Znth i edges d = (u + 1, v + 1) ->
    0 <= u < n -> 0 <= v < n ->
    CurrentEdgeFresh edges i ->
    AdjacencyBuildState n edges i head_data to_data next_data ->
    AdjacencyBuildState n edges (i + 1)
      (replace_Znth v (2 * i + 1) (replace_Znth u (2 * i) head_data))
      (to_data ++ v :: u :: nil)
      (next_data ++ Znth u head_data (-1) ::
        Znth v (replace_Znth u (2 * i) head_data) (-1) :: nil).
Proof.
  intros n edges i head_data to_data next_data u v d Hi Hedge_i Hu Hv Hfresh Hstate.
  unfold AdjacencyBuildState in Hstate.
  destruct Hstate as
    [Hdone [Hhead [Hto [Hnext [Hheads [Hslots [Hedge_model Hunique]]]]]]].
  unfold CurrentEdgeFresh in Hfresh. specialize (Hfresh Hi).
  replace (Znth i edges (0, 0)) with (Znth i edges d) in Hfresh.
  2:{ apply Znth_indep. exact Hi. }
  rewrite Hedge_i in Hfresh. simpl in Hfresh.
  destruct Hfresh as [Huv Hnot].
  set (head1 := replace_Znth u (2 * i) head_data).
  set (head2 := replace_Znth v (2 * i + 1) head1).
  set (to2 := to_data ++ v :: u :: nil).
  set (next2 := next_data ++ Znth u head_data (-1) ::
    Znth v head1 (-1) :: nil).
  assert (Hhead1 : Zlength head1 = n).
  { unfold head1. rewrite Zlength_replace_Znth__solver_build_step. exact Hhead. }
  assert (Hhead2 : Zlength head2 = n).
  { unfold head2. rewrite Zlength_replace_Znth__solver_build_step. exact Hhead1. }
  assert (Hto2 : Zlength to2 = 2 * i + 2).
  { unfold to2. repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
    rewrite Zlength_nil, Hto. lia. }
  assert (Hnext2 : Zlength next2 = 2 * i + 2).
  { unfold next2. repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
    rewrite Zlength_nil, Hnext. lia. }
  assert (Hhead1_v : Znth v head1 (-1) = Znth v head_data (-1)).
  { unfold head1. apply Znth_replace_diff__solver_build_step;
      rewrite ?Hhead; lia. }
  assert (Hnext_bounds : forall slot, 0 <= slot < 2 * i ->
      Znth slot next_data (-1) = -1 \/
      0 <= Znth slot next_data (-1) < slot).
  { intros slot Hslot. exact (proj2 (Hslots slot Hslot)). }
  assert (Hslot_iff : forall x slot,
      AdjacencySlot head2 next2 x slot <->
      AdjacencySlot head_data next_data x slot \/
      (x = u /\ slot = 2 * i) \/
      (x = v /\ slot = 2 * i + 1)).
  { intros x slot. unfold head2, next2, head1.
    apply (adjacency_slot_push_iff__solver_build_step
      n i head_data next_data u v); try assumption; lia. }
  assert (Hno_old_edge :
      ~ (In (u + 1, v + 1) (sublist 0 i edges) \/
         In (v + 1, u + 1) (sublist 0 i edges))).
  { intros [Hin | Hin]; apply Hnot.
    - apply in_map. exact Hin.
    - pose proof (in_map CanonicalEdge (sublist 0 i edges)
        (v + 1, u + 1) Hin) as Hmapped.
      rewrite canonical_swap__solver_build_step in Hmapped. exact Hmapped. }
  unfold AdjacencyBuildState.
  change (0 <= i + 1 <= Zlength edges /\
    Zlength head2 = n /\ Zlength to2 = 2 * (i + 1) /\
    Zlength next2 = 2 * (i + 1) /\
    (forall x, 0 <= x < n ->
      Znth x head2 (-1) = -1 \/
      0 <= Znth x head2 (-1) < 2 * (i + 1)) /\
    (forall slot, 0 <= slot < 2 * (i + 1) ->
      0 <= Znth slot to2 0 < n /\
      (Znth slot next2 (-1) = -1 \/
       0 <= Znth slot next2 (-1) < slot)) /\
    (forall x y, 0 <= x < n -> 0 <= y < n ->
      (In (x + 1, y + 1) (sublist 0 (i + 1) edges) \/
       In (y + 1, x + 1) (sublist 0 (i + 1) edges) <->
       exists slot, AdjacencySlot head2 next2 x slot /\
         Znth slot to2 0 = y)) /\
    forall x slot1 slot2,
      AdjacencySlot head2 next2 x slot1 ->
      AdjacencySlot head2 next2 x slot2 ->
      Znth slot1 to2 0 = Znth slot2 to2 0 ->
      slot1 = slot2).
  split; [lia |]. split; [exact Hhead2 |].
  split; [lia |]. split; [lia |]. split; [| split; [| split]].
  - intros x Hx.
    destruct (Z.eq_dec x u) as [-> | Hxu].
    + right. unfold head2, head1.
      rewrite Znth_replace_diff__solver_build_step by
        (rewrite ?Zlength_replace_Znth__solver_build_step, ?Hhead; lia).
      rewrite Znth_replace_Znth_Same by (rewrite Hhead; lia). lia.
    + destruct (Z.eq_dec x v) as [-> | Hxv].
      * right. unfold head2. rewrite Znth_replace_Znth_Same by (rewrite Hhead1; lia).
        lia.
      * unfold head2. fold head1.
        rewrite Znth_replace_Znth_Diff by (try rewrite Hhead1; lia).
        unfold head1.
        rewrite Znth_replace_Znth_Diff by (try rewrite Hhead; lia).
        specialize (Hheads x Hx). destruct Hheads; [left | right]; lia.
  - intros slot0 Hslot.
    destruct (Z_lt_ge_dec slot0 (2 * i)) as [Hold | Hnew].
    + specialize (Hslots slot0 ltac:(lia)). destruct Hslots as [Hto_bounds Hnext_bound].
      split.
      * unfold to2. rewrite Znth_app_left__solver_build_step by (rewrite Hto; lia).
        exact Hto_bounds.
      * unfold next2. rewrite Znth_app_left__solver_build_step by (rewrite Hnext; lia).
        exact Hnext_bound.
    + assert (slot0 = 2 * i \/ slot0 = 2 * i + 1) by lia.
      destruct H as [-> | ->].
      * split.
        -- unfold to2. replace (2 * i) with (Zlength to_data) by lia.
           rewrite Znth_app_two_first__solver_build_step. exact Hv.
        -- unfold next2. replace (2 * i) with (Zlength next_data) by lia.
           rewrite Znth_app_two_first__solver_build_step.
           specialize (Hheads u Hu). destruct Hheads; [left | right]; lia.
      * split.
        -- unfold to2. replace (2 * i + 1) with (Zlength to_data + 1) by lia.
           rewrite Znth_app_two_second__solver_build_step. exact Hu.
        -- unfold next2. replace (2 * i + 1) with (Zlength next_data + 1) by lia.
           rewrite Znth_app_two_second__solver_build_step, Hhead1_v.
           specialize (Hheads v Hv). destruct Hheads; [left | right]; lia.
  - intros x y Hx Hy.
    rewrite sublist_prefix_succ__solver_build_step with (d := d) by exact Hi.
    rewrite Hedge_i. repeat rewrite in_app_iff. simpl.
    split.
    + intros [[Hold | [Hxy | Hfalse]] | [Hold | [Hyx | Hfalse]]]; try contradiction.
      * destruct (proj1 (Hedge_model x y Hx Hy) (or_introl Hold))
          as [slot [Hslot Hval]].
        exists slot. split; [apply Hslot_iff; left; exact Hslot |].
        unfold to2. rewrite Znth_app_left__solver_build_step by
          (rewrite Hto; destruct Hslot as [_ [Hb _]]; lia).
        exact Hval.
      * injection Hxy as Hxq Hyq.
        assert (x = u) by lia. assert (y = v) by lia. subst x y.
        exists (2 * i). split.
        -- apply Hslot_iff. right. left. auto.
        -- unfold to2. replace (2 * i) with (Zlength to_data) by lia.
           apply Znth_app_two_first__solver_build_step.
      * destruct (proj1 (Hedge_model x y Hx Hy) (or_intror Hold))
          as [slot [Hslot Hval]].
        exists slot. split; [apply Hslot_iff; left; exact Hslot |].
        unfold to2. rewrite Znth_app_left__solver_build_step by
          (rewrite Hto; destruct Hslot as [_ [Hb _]]; lia).
        exact Hval.
      * injection Hyx as Hyq Hxq.
        assert (x = v) by lia. assert (y = u) by lia. subst x y.
        exists (2 * i + 1). split.
        -- apply Hslot_iff. right. right. auto.
        -- unfold to2. replace (2 * i + 1) with (Zlength to_data + 1) by lia.
           apply Znth_app_two_second__solver_build_step.
    + intros [slot [Hslot Hval]]. apply Hslot_iff in Hslot.
      destruct Hslot as [Holdslot | [[-> ->] | [-> ->]]].
      * pose proof (proj2 (Hedge_model x y Hx Hy)) as Hold_edge.
        assert (Hedge_old : In (x + 1, y + 1) (sublist 0 i edges) \/
            In (y + 1, x + 1) (sublist 0 i edges)).
        { apply Hold_edge. exists slot. split; [exact Holdslot |].
          unfold to2 in Hval. rewrite Znth_app_left__solver_build_step in Hval
            by (rewrite Hto; destruct Holdslot as [_ [Hb _]]; lia).
          exact Hval. }
        destruct Hedge_old as [Hedge_old | Hedge_old].
        -- left. left. exact Hedge_old.
        -- right. left. exact Hedge_old.
      * unfold to2 in Hval. replace (2 * i) with (Zlength to_data) in Hval by lia.
        rewrite Znth_app_two_first__solver_build_step in Hval. subst y.
        left. right. auto.
      * unfold to2 in Hval. replace (2 * i + 1) with (Zlength to_data + 1) in Hval by lia.
        rewrite Znth_app_two_second__solver_build_step in Hval. subst y.
        right. right. auto.
  - intros x slot1 slot2 Hs1 Hs2 Hval.
    rewrite Hslot_iff in Hs1, Hs2.
    destruct Hs1 as [Hold1 | [[Hx1 Hslot1] | [Hx1 Hslot1]]];
    destruct Hs2 as [Hold2 | [[Hx2 Hslot2] | [Hx2 Hslot2]]].
    + apply (Hunique x slot1 slot2 Hold1 Hold2).
      unfold to2 in Hval.
      rewrite !Znth_app_left__solver_build_step in Hval
        by (destruct Hold1 as [_ [Hb1 _]]; destruct Hold2 as [_ [Hb2 _]];
            rewrite Hnext in Hb1, Hb2; rewrite Hto; lia).
      exact Hval.
    + subst x slot2. exfalso. apply Hno_old_edge.
      apply (proj2 (Hedge_model u v Hu Hv)). exists slot1. split; [exact Hold1 |].
      unfold to2 in Hval. rewrite Znth_app_left__solver_build_step in Hval at 1
        by (destruct Hold1 as [_ [Hb _]]; rewrite Hto, <- Hnext; exact Hb).
      replace (2 * i) with (Zlength to_data) in Hval by lia.
      rewrite Znth_app_two_first__solver_build_step in Hval. exact Hval.
    + subst x slot2. exfalso. apply Hno_old_edge.
      assert (Hedge_vu : In (v + 1, u + 1) (sublist 0 i edges) \/
          In (u + 1, v + 1) (sublist 0 i edges)).
      { apply (proj2 (Hedge_model v u Hv Hu)). exists slot1. split; [exact Hold1 |].
        unfold to2 in Hval. rewrite Znth_app_left__solver_build_step in Hval at 1
          by (destruct Hold1 as [_ [Hb _]]; rewrite Hto, <- Hnext; exact Hb).
        replace (2 * i + 1) with (Zlength to_data + 1) in Hval by lia.
        rewrite Znth_app_two_second__solver_build_step in Hval. exact Hval. }
      destruct Hedge_vu; auto.
    + subst x slot1. exfalso. apply Hno_old_edge.
      apply (proj2 (Hedge_model u v Hu Hv)). exists slot2. split; [exact Hold2 |].
      symmetry in Hval. unfold to2 in Hval.
      rewrite Znth_app_left__solver_build_step in Hval at 1
        by (destruct Hold2 as [_ [Hb _]]; rewrite Hto, <- Hnext; exact Hb).
      replace (2 * i) with (Zlength to_data) in Hval by lia.
      rewrite Znth_app_two_first__solver_build_step in Hval. exact Hval.
    + congruence.
    + subst x slot1. subst slot2. exfalso. apply Huv. lia.
    + subst x slot1. exfalso. apply Hno_old_edge.
      assert (Hedge_vu : In (v + 1, u + 1) (sublist 0 i edges) \/
          In (u + 1, v + 1) (sublist 0 i edges)).
      { apply (proj2 (Hedge_model v u Hv Hu)). exists slot2. split; [exact Hold2 |].
        symmetry in Hval. unfold to2 in Hval.
        rewrite Znth_app_left__solver_build_step in Hval at 1
          by (destruct Hold2 as [_ [Hb _]]; rewrite Hto, <- Hnext; exact Hb).
        replace (2 * i + 1) with (Zlength to_data + 1) in Hval by lia.
        rewrite Znth_app_two_second__solver_build_step in Hval. exact Hval. }
      destruct Hedge_vu; auto.
    + subst x slot1. subst slot2. exfalso. apply Huv. lia.
    + congruence.
Qed.
Lemma degree_prefix_extend__solver_build_step :
  forall n edges i degrees u v d,
    0 <= i < Zlength edges ->
    Znth i edges d = (u + 1, v + 1) ->
    0 <= u < n -> 0 <= v < n -> u <> v ->
    DegreePrefix n edges i degrees ->
    DegreePrefix n edges (i + 1)
      (replace_Znth v
        (Znth v
          (replace_Znth u (Znth u degrees 0 + 1) degrees) 0 + 1)
        (replace_Znth u (Znth u degrees 0 + 1) degrees)).
Proof.
  intros n edges i degrees u v d Hi Hedge Hu Hv Huv [Hlen Hprefix].
  split.
  - repeat rewrite Zlength_replace_Znth__solver_build_step.
    exact Hlen.
  - intros x Hx.
    rewrite sublist_prefix_succ__solver_build_step with (d := d) by exact Hi.
    unfold Degree in Hprefix |- *.
    rewrite filter_app, Zlength_app.
    simpl. rewrite Hedge. simpl.
    rewrite <- (Hprefix x Hx).
    destruct (Z.eq_dec x u) as [-> | Hxu].
    + rewrite Znth_replace_diff__solver_build_step by
        (repeat rewrite Zlength_replace_Znth__solver_build_step; try rewrite Hlen; lia).
      rewrite Znth_replace_same__solver_build_step by (rewrite Hlen; lia).
      rewrite Z.eqb_refl. simpl.
      change (Znth u degrees 0 + 1 = Znth u degrees 0 + 1).
      reflexivity.
    + destruct (Z.eq_dec x v) as [-> | Hxv].
      * rewrite Znth_replace_same__solver_build_step by
          (rewrite Zlength_replace_Znth__solver_build_step, Hlen; lia).
        rewrite Znth_replace_diff__solver_build_step by
          (repeat rewrite Zlength_replace_Znth__solver_build_step; try rewrite Hlen; lia).
        destruct (Z.eqb_spec (u + 1) (v + 1));
          [exfalso; apply Huv; lia | simpl].
        rewrite Z.eqb_refl. simpl.
        change (Znth v degrees 0 + 1 = Znth v degrees 0 + 1).
        reflexivity.
      * rewrite Znth_replace_diff__solver_build_step by
          (repeat rewrite Zlength_replace_Znth__solver_build_step; try rewrite Hlen; lia).
        rewrite Znth_replace_diff__solver_build_step by (try rewrite Hlen; lia).
        destruct (Z.eqb_spec (u + 1) (x + 1));
          [exfalso; apply Hxu; lia | simpl].
        destruct (Z.eqb_spec (v + 1) (x + 1));
          [exfalso; apply Hxv; lia | simpl].
        rewrite Zlength_nil. lia.
Qed.
Lemma adjacency_build_complete__solver_build_finish :
  forall n edges head_data to_data next_data,
  Zlength edges = n - 1 ->
  AdjacencyBuildState n edges (n - 1)
    head_data to_data next_data ->
  AdjacencyModel n edges head_data to_data next_data.
Proof.
  intros n edges head_data to_data next_data Hedges Hbuild.
  unfold AdjacencyBuildState in Hbuild.
  destruct Hbuild as
    (Hdone & Hhead & Hto & Hnext & Hheads & Hslots & Hadj & Hunique).
  unfold AdjacencyModel.
  split; [exact Hhead|].
  split; [lia|].
  split; [lia|].
  split; [exact Hedges|].
  split.
  - intros u Hu. specialize (Hheads u Hu).
    destruct Hheads as [Hnone | Hsome].
    + left. exact Hnone.
    + right. lia.
  - split.
    + intros slot Hslot. apply Hslots. lia.
    + split.
      * intros u v Hu Hv.
        specialize (Hadj u v Hu Hv).
        rewrite (sublist_self edges (n - 1) (eq_sym Hedges)) in Hadj.
        exact Hadj.
      * exact Hunique.
Qed.
Lemma ancestor_after_extend__solver_bfs_pipeline :
  forall parents start steps vertex,
    0 <= steps ->
    0 <= vertex < Zlength parents ->
    AncestorAfter parents start steps vertex ->
    AncestorAfter parents start (steps + 1) (Znth vertex parents 0).
Proof.
  intros parents start steps vertex Hsteps Hvertex Hancestor.
  destruct Hancestor as [path [Hlength [Hstart [Hend Hnext]]]].
  unfold AncestorAfter.
  exists (path ++ (Znth vertex parents 0 :: nil)).
  split.
  - rewrite Zlength_app_cons, Hlength. lia.
  - split.
    + rewrite app_Znth1 by lia. exact Hstart.
    + split.
      * rewrite app_Znth2 by lia.
        rewrite Hlength.
        replace (steps + 1 - (steps + 1)) with 0 by lia.
        rewrite Znth0_cons.
        reflexivity.
      * intros j Hj.
        destruct (Z_lt_ge_dec j steps) as [Hbefore | Hlast].
        -- rewrite app_Znth1 by lia.
           rewrite app_Znth1 by lia.
           apply Hnext. lia.
        -- assert (j = steps) by lia. subst j.
           rewrite app_Znth2 by lia.
           rewrite app_Znth1 by lia.
           rewrite Hlength.
           replace (steps + 1 - (steps + 1)) with 0 by lia.
           rewrite Znth0_cons, Hend.
           rewrite (Znth_indep parents vertex 0 (-1)) by exact Hvertex.
           reflexivity.
Qed.
Lemma graph_distance_self_zero__solver_bfs_pipeline :
  forall edges source distance,
    GraphDistance edges source source distance ->
    distance = 0.
Proof.
  intros edges source distance Hdistance.
  unfold GraphDistance in Hdistance.
  destruct Hdistance as [path [[Hvalid Hnodup] [Hvalue Hminimal]]].
  assert (Htrivial :
    HedgehogPath edges source source (source :: nil)).
  {
    unfold HedgehogPath.
    split.
    - apply valid_vpath_empty.
    - constructor; [simpl; tauto | constructor].
  }
  specialize (Hminimal (source :: nil) Htrivial).
  assert (Hpositive : 1 <= Zlength path).
  {
    destruct path as [|x xs].
    - exfalso.
      pose proof (valid_vpath_not_nil
        (HedgehogGraph edges) source nil source Hvalid) as Hnotnil.
      apply Hnotnil. reflexivity.
    - rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
  }
  rewrite Zlength_cons, Zlength_nil in Hminimal.
  lia.
Qed.
Lemma ancestor_parent_bounds__solver_bfs_pipeline :
  forall n edges source parents distances endpoint k steps vertex out,
    BFSResult n edges source parents distances endpoint ->
    DiameterDecision k distances endpoint out ->
    out <> 0 ->
    1 <= k ->
    0 <= steps < k ->
    0 <= vertex < n ->
    AncestorAfter parents endpoint steps vertex ->
    0 <= Znth vertex parents 0 < n.
Proof.
  intros n edges source parents distances endpoint k steps vertex out
    Hresult Hdiameter Hout Hk Hsteps Hvertex Hancestor.
  unfold DiameterDecision in Hdiameter.
  destruct Hdiameter as [[Hout0 Hne] | [Hout1 Hdiameter]].
  - contradiction.
  - unfold BFSResult in Hresult.
    destruct Hresult as [Hdata [Hendpoint Hfarthest]].
    unfold BFSData in Hdata.
    destruct Hdata as
      [Hparents_len [Hdistances_len [Hsource [Hparent_state Hdistance]]]].
    unfold BFSParentState in Hparent_state.
    destruct Hparent_state as [Hsource_parent Hparent_step].
    assert (Hsource_distance : Znth source distances (-1) = 0).
    {
      pose proof (Hdistance source Hsource) as Hself.
      exact (graph_distance_self_zero__solver_bfs_pipeline
        edges (source + 1) (Znth source distances (-1)) Hself).
    }
    destruct Hancestor as [path [Hpath_len [Hpath_start [Hpath_end Hpath_step]]]].
    assert (Hchain : forall m : nat,
      Z.of_nat m <= steps ->
      0 <= Znth (Z.of_nat m) path 0 < n /\
      Znth (Znth (Z.of_nat m) path 0) distances (-1) =
        2 * k - Z.of_nat m).
    {
      intro m.
      induction m as [|m IH].
      - intros Hm.
        rewrite Nat2Z.inj_0, Hpath_start.
        split; [exact Hendpoint |].
        rewrite <- (Znth_indep distances endpoint 0 (-1)) by
          (rewrite Hdistances_len; exact Hendpoint).
        lia.
      - intros Hm.
        replace (Z.of_nat (S m)) with (Z.of_nat m + 1) in Hm |- * by lia.
        specialize (IH ltac:(lia)).
        destruct IH as [Hcurrent_bounds Hcurrent_distance].
        assert (Hcurrent_not_source :
          Znth (Z.of_nat m) path 0 <> source).
        {
          intros Heq.
          rewrite Heq, Hsource_distance in Hcurrent_distance.
          lia.
        }
        pose proof (Hparent_step
          (Znth (Z.of_nat m) path 0)
          Hcurrent_bounds Hcurrent_not_source ltac:(lia)) as Hparent.
        destruct Hparent as [Hparent_bounds [Hedge Hdistance_step]].
        pose proof (Hpath_step (Z.of_nat m) ltac:(lia)) as Hpath_next.
        rewrite Hpath_next.
        split.
        + exact Hparent_bounds.
        + lia.
    }
    specialize (Hchain (Z.to_nat steps)).
    rewrite Z2Nat.id in Hchain by lia.
    specialize (Hchain ltac:(lia)).
    destruct Hchain as [Hchain_bounds Hvertex_distance].
    rewrite Hpath_end in Hchain_bounds, Hvertex_distance.
    assert (Hvertex_not_source : vertex <> source).
    {
      intros Heq.
      rewrite Heq, Hsource_distance in Hvertex_distance.
      lia.
    }
    pose proof (Hparent_step vertex Hvertex Hvertex_not_source ltac:(lia))
      as Hparent.
    destruct Hparent as [Hparent_bounds [Hedge Hdistance_step]].
    rewrite (Znth_indep parents vertex 0 (-1)) by
      (rewrite Hparents_len; exact Hvertex).
    exact Hparent_bounds.
Qed.
Lemma solver_decision_reject_next__solver_decision_reject :
  forall n k edges second_parent second_dist endpoint center
         center_parent center_dist degrees done ok,
    0 <= done ->
    ~ HedgehogVertexOK k center done
        (Znth done center_dist (-1)) (Znth done degrees 0) ->
    SolverDecision n k edges second_parent second_dist endpoint center
      center_parent center_dist degrees done ok ->
    SolverDecision n k edges second_parent second_dist endpoint center
      center_parent center_dist degrees (done + 1) 0.
Proof.
  intros n k edges second_parent second_dist endpoint center
    center_parent center_dist degrees done ok Hdone Hbad Hdecision.
  unfold SolverDecision in Hdecision |- *.
  destruct Hdecision as [[Hout Hdiameter] |
    [Hdiameter [Hancestor [Hbfs Hprefix]]]].
  - left. split; [reflexivity | exact Hdiameter].
  - right.
    split; [exact Hdiameter |].
    split; [exact Hancestor |].
    split; [exact Hbfs |].
    unfold DecisionPrefix.
    split.
    + left. reflexivity.
    + split.
      * intros Hzero. lia.
      * intros Hall.
        exfalso.
        apply Hbad.
        apply Hall.
        lia.
Qed.
Lemma hedgehog_internal_noncenter__solver_decision_accept :
  forall k center vertex distance degree,
    distance < k -> vertex <> center -> 4 <= degree ->
    HedgehogVertexOK k center vertex distance degree.
Proof.
  intros k center vertex distance degree Hdist Hnoncenter Hdegree.
  unfold HedgehogVertexOK.
  split; [lia |]. split.
  - intros. lia.
  - intros. split.
    + intros. contradiction.
    + intros. exact Hdegree.
Qed.
Lemma hedgehog_internal_center__solver_decision_accept :
  forall k center vertex distance degree,
    distance < k -> vertex = center -> 3 <= degree ->
    HedgehogVertexOK k center vertex distance degree.
Proof.
  intros k center vertex distance degree Hdist Hcenter Hdegree.
  unfold HedgehogVertexOK.
  split; [lia |]. split.
  - intros. lia.
  - intros. split.
    + intros. exact Hdegree.
    + intros. contradiction.
Qed.
Lemma hedgehog_boundary_leaf__solver_decision_accept :
  forall k center vertex distance degree,
    distance = k -> degree = 1 ->
    HedgehogVertexOK k center vertex distance degree.
Proof.
  intros k center vertex distance degree Hdist Hdegree.
  unfold HedgehogVertexOK.
  split; [lia |]. split.
  - intros. exact Hdegree.
  - intros. lia.
Qed.
Lemma hedgehog_internal_noncenter_failure__solver_decision_accept :
  forall k center vertex distance degree,
    distance < k -> vertex <> center -> degree < 4 ->
    ~ HedgehogVertexOK k center vertex distance degree.
Proof.
  intros k center vertex distance degree Hdist Hnoncenter Hdegree Hok.
  unfold HedgehogVertexOK in Hok.
  destruct Hok as [_ [_ Hinternal]].
  specialize (Hinternal Hdist).
  destruct Hinternal as [_ Hnoncenter_degree].
  specialize (Hnoncenter_degree Hnoncenter).
  lia.
Qed.
Lemma solver_decision_advance_pass__solver_decision_accept :
  forall n k edges second_parent second_dist endpoint center
    center_parent center_dist degrees done out,
    0 <= done < n ->
    out <> 0 ->
    SolverDecision n k edges second_parent second_dist endpoint center
      center_parent center_dist degrees done out ->
    HedgehogVertexOK k center done
      (Znth done center_dist 0) (Znth done degrees 0) ->
    SolverDecision n k edges second_parent second_dist endpoint center
      center_parent center_dist degrees (done + 1) out.
Proof.
  intros n k edges second_parent second_dist endpoint center
    center_parent center_dist degrees done out Hdone Hout Hdecision Hcurrent.
  unfold SolverDecision in Hdecision |- *.
  destruct Hdecision as [[Hzero Hdiameter_bad] |
    [Hdiameter [Hancestor [Hbfs Hprefix]]]].
  - contradiction.
  - right. split; [exact Hdiameter |].
    split; [exact Hancestor |]. split; [exact Hbfs |].
    unfold BFSData in Hbfs.
    destruct Hbfs as [_ [Hdist_len _]].
    rewrite <- (Znth_indep center_dist done (-1) 0) in Hcurrent
      by (rewrite Hdist_len; exact Hdone).
    unfold DecisionPrefix in Hprefix |- *.
    destruct Hprefix as [Hout_value Hiff].
    assert (Hout_one : out = 1).
    { destruct Hout_value; [contradiction | assumption]. }
    split.
    + exact Hout_value.
    + split.
      * intros _. intros vertex Hvertex.
        destruct (Z.lt_ge_cases vertex done).
        -- apply (proj1 Hiff Hout_one vertex). lia.
        -- assert (vertex = done) by lia. subst vertex. exact Hcurrent.
      * intros _. exact Hout_one.
Qed.
Lemma solver_decision_advance_fail__solver_decision_accept :
  forall n k edges second_parent second_dist endpoint center
    center_parent center_dist degrees done out,
    0 <= done < n ->
    out <> 0 ->
    SolverDecision n k edges second_parent second_dist endpoint center
      center_parent center_dist degrees done out ->
    ~ HedgehogVertexOK k center done
      (Znth done center_dist 0) (Znth done degrees 0) ->
    SolverDecision n k edges second_parent second_dist endpoint center
      center_parent center_dist degrees (done + 1) 0.
Proof.
  intros n k edges second_parent second_dist endpoint center
    center_parent center_dist degrees done out Hdone Hout Hdecision Hcurrent.
  unfold SolverDecision in Hdecision |- *.
  destruct Hdecision as [[Hzero Hdiameter_bad] |
    [Hdiameter [Hancestor [Hbfs Hprefix]]]].
  - contradiction.
  - right. split; [exact Hdiameter |].
    split; [exact Hancestor |]. split; [exact Hbfs |].
    unfold BFSData in Hbfs.
    destruct Hbfs as [_ [Hdist_len _]].
    assert (Hcurrent_minus :
      ~ HedgehogVertexOK k center done
        (Znth done center_dist (-1)) (Znth done degrees 0)).
    {
      rewrite (Znth_indep center_dist done (-1) 0)
        by (rewrite Hdist_len; exact Hdone).
      exact Hcurrent.
    }
    unfold DecisionPrefix.
    split.
    + left. reflexivity.
    + split.
      * intros Hbad. discriminate Hbad.
      * intros Hall. exfalso. apply Hcurrent_minus.
        apply Hall. lia.
Qed.
