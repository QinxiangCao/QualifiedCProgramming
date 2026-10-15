Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

#[local] Instance finite_vertex_pair (n : Z) :
    Finite (fun e : Z*Z =>
      1 <= fst e < n + 1 /\ 1 <= snd e < n + 1) :=
  Finite_prod (fun x : Z => 1 <= x < n + 1)
              (fun y : Z => 1 <= y < n + 1).

Definition EdgePresent (edges : list (Z*Z)) (removed : (Z*Z) -> Prop)
    (u v : Z) : Prop :=
  (In (u,v) edges \/ In (v,u) edges) /\ ~ removed (u,v) /\ ~ removed (v,u).

Definition ConnectedWithout (edges : list (Z*Z)) (removed : (Z*Z) -> Prop)
    (u v : Z) : Prop :=
  clos_refl_trans (EdgePresent edges removed) u v.

(** Canonical orientation of an undirected edge.  This lets the input-tree
    contract state loop freedom and duplicate freedom independently of the
    orientation used in the input list. *)
Definition CanonicalEdge (edge : Z*Z) : Z*Z :=
  (Z.min (fst edge) (snd edge), Z.max (fst edge) (snd edge)).

Definition SimpleUndirectedEdges (edges : list (Z*Z)) : Prop :=
  (forall edge, In edge edges -> fst edge <> snd edge) /\
  NoDup (map CanonicalEdge edges).

(** A discovery prefix is connected by edges that point strictly backward
    in the prefix.  This is the implementation-independent shape shared by
    breadth-first, depth-first, and other rooted discovery orders. *)
Definition ConnectedDiscoveryPrefix
    (edges : list (Z*Z)) (discovered : list Z) : Prop :=
  forall q,
    0 < q < Zlength discovered ->
    exists parent_pos,
      0 <= parent_pos < q /\
      (In (Znth q discovered 0 + 1,
           Znth parent_pos discovered 0 + 1) edges \/
       In (Znth parent_pos discovered 0 + 1,
           Znth q discovered 0 + 1) edges).

(** Global cut consequence of an undirected tree.  Once a fresh vertex is
    attached to a connected discovered prefix through [parent], none of its
    other neighbors lies in the prefix extended by that vertex.  Unlike a
    cursor-local freshness condition, this property relates adjacency lists
    of every vertex and is stable for any valid rooted discovery order. *)
Definition TreeAttachmentCut (edges : list (Z*Z)) : Prop :=
  forall discovered fresh parent neighbor,
    NoDup discovered ->
    ConnectedDiscoveryPrefix edges discovered ->
    ~ In fresh discovered ->
    In parent discovered ->
    (In (fresh + 1, parent + 1) edges \/
     In (parent + 1, fresh + 1) edges) ->
    (In (fresh + 1, neighbor + 1) edges \/
     In (neighbor + 1, fresh + 1) edges) ->
    neighbor <> parent ->
    ~ In neighbor (discovered ++ (fresh :: nil)).

(** Local projection consumed by one adjacency-build iteration.  It is
    implication-shaped so it remains meaningful at the loop's terminal
    cursor, where there is no current edge. *)
Definition CurrentEdgeFresh (edges : list (Z*Z)) (index : Z) : Prop :=
  0 <= index < Zlength edges ->
  let edge := Znth index edges (0, 0) in
  fst edge <> snd edge /\
  ~ In (CanonicalEdge edge)
      (map CanonicalEdge (sublist 0 index edges)).

Definition ValidRemoval (n k : Z) (edges : list (Z*Z))
    (removed : (Z*Z) -> Prop) : Prop :=
  (forall e, removed e -> In e edges) /\
  #(fun e : Z*Z =>
      (1 <= fst e < n + 1 /\ 1 <= snd e < n + 1) /\ removed e) = k.

Definition CutHasMinimumComponent (n x : Z) (edges : list (Z*Z))
    (removed : (Z*Z) -> Prop) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : Z * Z =>
      1 <= fst candidate <= n /\
      snd candidate = #(fun u : Z =>
        1 <= u < n + 1 /\ ConnectedWithout edges removed (fst candidate) u))
    snd x.

Definition Spec (n k : Z) (edges : list (Z*Z)) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : ((Z*Z) -> Prop) * Z =>
      ValidRemoval n k edges (fst candidate) /\
      CutHasMinimumComponent n (snd candidate) edges (fst candidate))
    snd out.

(** A threshold is feasible exactly when it does not exceed the optimum.
    This is the implementation-independent decision predicate exposed by
    [feasible] to the binary search. *)
Definition ThresholdFeasible
    (n k : Z) (edges : list (Z*Z)) (minimum : Z) : Prop :=
  exists optimum,
    Spec n k edges optimum /\ minimum <= optimum.

(** The linked-list cursor relation induced by [next_data]. *)
Definition AdjacencyNext (next_data : list Z) (from to : Z) : Prop :=
  0 <= from < Zlength next_data /\
  to = Znth from next_data (-1).

Definition AdjacencySlot
    (head_data next_data : list Z) (u slot : Z) : Prop :=
  0 <= u < Zlength head_data /\
  0 <= slot < Zlength next_data /\
  clos_refl_trans (AdjacencyNext next_data)
    (Znth u head_data (-1)) slot.

(** Prefix representation while the adjacency arrays are being built. *)
Definition AdjacencyBuildState
    (n : Z) (edges : list (Z*Z)) (done : Z)
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

(** Exact mathematical interpretation of the three flat adjacency arrays.
    Vertices in [edges] are one-based; array vertices are zero-based. *)
Definition AdjacencyModel
    (n : Z) (edges : list (Z*Z))
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

(** Prefix state of the iterative rooted traversal.  [order_data] is exactly
    the discovered sequence, while [parent_cells] records which scattered
    parent-array cells have been initialized. *)
Definition TraversalState
    (n : Z) (edges : list (Z*Z)) (processed : Z)
    (order_data : list Z) (parent_cells : list (option Z)) : Prop :=
  Zlength parent_cells = n /\
  0 <= processed <= Zlength order_data /\
  1 <= Zlength order_data <= n /\
  NoDup order_data /\
  Znth 0 order_data 0 = 0 /\
  (forall q,
    0 <= q < Zlength order_data ->
    let vertex := Znth q order_data 0 in
    0 <= vertex < n /\
    exists parent_vertex,
      Znth vertex parent_cells None = Some parent_vertex /\
      ((q = 0 /\ parent_vertex = -1) \/
       exists parent_pos,
         0 <= parent_pos < q /\
         parent_vertex = Znth parent_pos order_data 0 /\
         (In (vertex + 1, parent_vertex + 1) edges \/
          In (parent_vertex + 1, vertex + 1) edges))) /\
  (forall q neighbor,
    0 <= q < processed ->
    (In (Znth q order_data 0 + 1, neighbor + 1) edges \/
     In (neighbor + 1, Znth q order_data 0 + 1) edges) ->
    In neighbor order_data) /\
  forall q neighbor parent_vertex,
    processed < q < Zlength order_data ->
    Znth (Znth q order_data 0) parent_cells None = Some parent_vertex ->
    (In (Znth q order_data 0 + 1, neighbor + 1) edges \/
     In (neighbor + 1, Znth q order_data 0 + 1) edges) ->
    neighbor <> parent_vertex ->
    ~ In neighbor order_data.

(** State at the boundary before scanning the current vertex.  The pending
    clause in [TraversalState] deliberately starts strictly after
    [processed], because children discovered while scanning the current
    vertex are appended to [order_data].  At entry, however, every
    non-parent neighbor of that current vertex is still undiscovered. *)
Definition TraversalEntryState
    (n : Z) (edges : list (Z*Z)) (processed : Z)
    (order_data : list Z) (parent_cells : list (option Z)) : Prop :=
  TraversalState n edges processed order_data parent_cells /\
  (processed < Zlength order_data ->
   let vertex := Znth processed order_data 0 in
   exists parent_vertex,
     Znth vertex parent_cells None = Some parent_vertex /\
     forall neighbor,
       (In (vertex + 1, neighbor + 1) edges \/
        In (neighbor + 1, vertex + 1) edges) ->
       neighbor <> parent_vertex ->
       ~ In neighbor order_data).

Definition TraversalAdjState
    (n : Z) (edges : list (Z*Z))
    (processed : Z) (order_data : list Z)
    (parent_cells : list (option Z))
    (head_data to_data next_data : list Z)
    (vertex parent_vertex cursor : Z) : Prop :=
  TraversalState n edges processed order_data parent_cells /\
  (-1 <= cursor < 2 * n - 2) /\
  0 <= vertex < n /\
  Znth vertex parent_cells None = Some parent_vertex /\
  (cursor = -1 \/
   AdjacencySlot head_data next_data vertex cursor) /\
  (forall slot,
    AdjacencySlot head_data next_data vertex slot ->
    (cursor = -1 \/
     ~ clos_refl_trans (AdjacencyNext next_data) cursor slot) ->
    In (Znth slot to_data 0) order_data) /\
  (forall slot,
    AdjacencySlot head_data next_data vertex slot ->
    clos_refl_trans (AdjacencyNext next_data) cursor slot ->
    Znth slot to_data 0 <> parent_vertex ->
    ~ In (Znth slot to_data 0) order_data) /\
  (cursor <> -1 ->
    0 <= Znth cursor to_data 0 < n) /\
  (cursor <> -1 -> Znth cursor to_data 0 <> parent_vertex ->
    ~ In (Znth cursor to_data 0) order_data /\
    Zlength order_data < n) /\
  (cursor = -1 ->
    forall neighbor,
      (In (vertex + 1, neighbor + 1) edges \/
       In (neighbor + 1, vertex + 1) edges) ->
      In neighbor order_data).

(** Completed rooted traversal: [order_data] is a permutation of all
    zero-based vertices and every non-root vertex names an earlier adjacent
    parent.  This characterizes the mathematical tree order without fixing a
    particular DFS/BFS implementation. *)
Definition RootedOrderModel
    (n : Z) (edges : list (Z*Z))
    (parent_data order_data : list Z) : Prop :=
  1 <= n /\
  Zlength parent_data = n /\
  Zlength order_data = n /\
  Permutation order_data (map Z.of_nat (seq 0 (Z.to_nat n))) /\
  Znth 0 order_data 0 = 0 /\
  Znth 0 parent_data (-1) = -1 /\
  forall q,
    1 <= q < n ->
    exists parent_pos,
      0 <= parent_pos < q /\
      Znth (Znth q order_data 0) parent_data (-1) =
        Znth parent_pos order_data 0 /\
      (In (Znth q order_data 0 + 1,
           Znth parent_pos order_data 0 + 1) edges \/
       In (Znth parent_pos order_data 0 + 1,
           Znth q order_data 0 + 1) edges).

(** Bounds needed at one reverse-scan program point.  The addition bound is
    deliberately about the current cursor only: after one child has been
    accumulated into a parent it need not hold simultaneously for an
    unprocessed sibling. *)
Definition CutScanNodeBounds
    (n cursor : Z) (parent_data order_data sizes : list Z) : Prop :=
  Zlength sizes = n /\
  (forall vertex, 0 <= vertex < n ->
    0 <= Znth vertex sizes 0 <= n) /\
  (0 <= cursor ->
    let vertex := Znth cursor order_data 0 in
    Znth vertex parent_data (-1) >= 0 ->
    Znth (Znth vertex parent_data (-1)) sizes 0 +
      Znth vertex sizes 0 <= n).

(** One mathematical reverse-scan update.  It records the two semantic
    choices made for the current rooted-tree vertex: whether its completed
    subtree forms a component, and whether the residual size is propagated
    to a parent. *)
Definition CutScanStep
    (n minimum cursor components : Z)
    (parent_data order_data sizes : list Z)
    (next_components : Z) (next_sizes : list Z) : Prop :=
  let vertex := Znth cursor order_data 0 in
  exists cut_sizes,
    ((Znth vertex sizes 0 >= minimum /\
      next_components = components + 1 /\
      cut_sizes = replace_Znth vertex 0 sizes) \/
     (Znth vertex sizes 0 < minimum /\
      next_components = components /\
      cut_sizes = sizes)) /\
    ((Znth vertex parent_data (-1) >= 0 /\
      next_sizes =
        replace_Znth (Znth vertex parent_data (-1))
          (Znth (Znth vertex parent_data (-1)) cut_sizes 0 +
           Znth vertex cut_sizes 0) cut_sizes) \/
     (Znth vertex parent_data (-1) < 0 /\
      next_sizes = cut_sizes)) /\
    CutScanNodeBounds n (cursor - 1)
      parent_data order_data next_sizes.

(** Relational continuation of the remaining reverse scan.  Unlike a
    terminal-only assertion, this relation is inductive at every cursor: a
    loop update exposes exactly the continuation required by the next
    invariant state. *)
Inductive ReverseCutScan
    (n minimum : Z) (parent_data order_data : list Z) :
    Z -> Z -> list Z -> Z -> list Z -> Prop :=
| reverse_cut_scan_done : forall components sizes,
    CutScanNodeBounds n (-1) parent_data order_data sizes ->
    ReverseCutScan n minimum parent_data order_data
      (-1) components sizes components sizes
| reverse_cut_scan_step : forall cursor components sizes
    next_components next_sizes final_components final_sizes,
    0 <= cursor ->
    CutScanNodeBounds n cursor parent_data order_data sizes ->
    CutScanStep n minimum cursor components parent_data order_data sizes
      next_components next_sizes ->
    ReverseCutScan n minimum parent_data order_data
      (cursor - 1) next_components next_sizes
      final_components final_sizes ->
    ReverseCutScan n minimum parent_data order_data
      cursor components sizes final_components final_sizes.

(** Mathematical bridge for the greedy reverse scan on any completed rooted
    order.  It is quantified over the all-ones input list, rather than tied to
    the concrete allocation history used to produce that list. *)
Definition CutScanReady
    (n k : Z) (edges : list (Z*Z))
    (parent_data order_data : list Z) : Prop :=
  forall minimum sizes,
    1 <= minimum <= n ->
    Zlength sizes = n ->
    (forall vertex, 0 <= vertex < n -> Znth vertex sizes 0 = 1) ->
    exists final_components final_sizes,
      ReverseCutScan n minimum parent_data order_data
        (n - 1) 0 sizes final_components final_sizes /\
      0 <= final_components <= n /\
      Zlength final_sizes = n /\
      (forall vertex, 0 <= vertex < n ->
        0 <= Znth vertex final_sizes 0 <= n) /\
      (final_components >= k + 1 <->
       ThresholdFeasible n k edges minimum).

(** The freshly allocated scratch buffer has an exact logical contents list,
    rather than merely an existential list of the right length. *)
Definition FreshSizeCells (n : Z) (cells : list (option Z)) : Prop :=
  cells = repeat None (Z.to_nat n).

(** Exact written prefix of the overwrite-to-one loop.  The matching C
    invariant owns this list as a concrete segment and owns the unprocessed
    suffix with [undef_seg], so every feasibility call may safely overwrite
    the whole scratch buffer regardless of its previous values. *)
Definition SizeInitializationState
    (n cursor : Z) (initialized : list Z) : Prop :=
  0 <= cursor <= n /\
  Zlength initialized = cursor /\
  forall j, 0 <= j < cursor -> Znth j initialized 0 = 1.

(** Valid inputs include the two implementation-independent existence facts
    consumed later: the bounded optimum and correctness of the greedy scan
    for any mathematical rooted order of the input tree. *)
Definition Pre (n k : Z) (edges : list (Z*Z)) : Prop :=
  1 <= k < n /\
  n <= 100000 /\
  Zlength edges = n - 1 /\
  Forall (fun e => 1 <= fst e <= n /\ 1 <= snd e <= n) edges /\
  SimpleUndirectedEdges edges /\
  TreeAttachmentCut edges /\
  (forall index, CurrentEdgeFresh edges index) /\
  (forall v, 1 <= v <= n ->
    ConnectedWithout edges (fun _ => False) 1 v) /\
  (exists optimum,
    Spec n k edges optimum /\ 1 <= optimum <= n / (k + 1)) /\
  forall parent_data order_data,
    RootedOrderModel n edges parent_data order_data ->
    CutScanReady n k edges parent_data order_data.

(** Reverse traversal state.  Every cursor owns a continuation to the same
    final component count, so both loop branches preserve the threshold
    decision without manufacturing a new fact at cursor zero. *)
Definition CutScanState
    (n k : Z) (edges : list (Z*Z))
    (minimum cursor components : Z)
    (parent_data order_data sizes : list Z) : Prop :=
  -1 <= cursor < n /\
  0 <= components <= n - 1 - cursor /\
  Zlength parent_data = n /\
  Zlength order_data = n /\
  RootedOrderModel n edges parent_data order_data /\
  CutScanNodeBounds n cursor parent_data order_data sizes /\
  exists final_components final_sizes,
    ReverseCutScan n minimum parent_data order_data
      cursor components sizes final_components final_sizes /\
    0 <= final_components <= n /\
    Zlength final_sizes = n /\
    (forall vertex, 0 <= vertex < n ->
      0 <= Znth vertex final_sizes 0 <= n) /\
    (final_components >= k + 1 <->
     ThresholdFeasible n k edges minimum).

(** Binary-search invariant stated against the mathematical optimum rather
    than against an executable mirror of the search loop. *)
Definition SearchState
    (n k : Z) (edges : list (Z*Z))
    (lo hi best : Z) : Prop :=
  1 <= lo <= n + 1 /\
  0 <= hi <= n /\
  1 <= best <= n /\
  exists optimum,
    Spec n k edges optimum /\
    1 <= optimum <= n /\
    1 <= best <= optimum /\
    ((lo <= optimum <= hi) \/
     (best = optimum /\ optimum < lo)).

Require Import Coq.micromega.Lia.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.micromega.Psatz.
Lemma size_initialization_complete__feasible_size_init :
  forall n cursor initialized,
    SizeInitializationState n cursor initialized ->
    cursor >= n ->
    cursor = n /\
    Zlength initialized = n /\
    forall j, 0 <= j < n -> Znth j initialized 0 = 1.
Proof.
  intros n cursor initialized Hstate Hdone.
  unfold SizeInitializationState in Hstate.
  destruct Hstate as [Hbounds [Hlength Hvalues]].
  assert (Hcursor : cursor = n) by lia.
  split; [exact Hcursor |].
  split; [lia |].
  intros j Hj.
  apply Hvalues.
  lia.
Qed.
Lemma Znth_app_left__feasible_size_init :
  forall (A : Type) (d : A) (left right : list A) i,
    0 <= i < Zlength left ->
    Znth i (left ++ right) d = Znth i left d.
Proof.
  intros A d left.
  induction left as [|x left IH]; intros right i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + reflexivity.
    + simpl.
      rewrite !Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hi.
      lia.
Qed.
Lemma Znth_app_last__feasible_size_init :
  forall (A : Type) (d x : A) (left : list A),
    Znth (Zlength left) (left ++ (x :: nil)) d = x.
Proof.
  intros A d x left.
  induction left as [|y left IH].
  - reflexivity.
  - simpl.
    rewrite Zlength_cons.
    rewrite Znth_cons by (pose proof (Zlength_nonneg left); lia).
    replace (Z.succ (Zlength left) - 1) with (Zlength left) by lia.
    exact IH.
Qed.
Lemma size_initialization_step__feasible_size_init :
  forall n cursor initialized,
    SizeInitializationState n cursor initialized ->
    cursor < n ->
    SizeInitializationState n (cursor + 1) (initialized ++ (1 :: nil)).
Proof.
  intros n cursor initialized Hstate Hcursor.
  unfold SizeInitializationState in *.
  destruct Hstate as [Hbounds [Hlength Hvalues]].
  split; [lia |].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros j Hj.
    destruct (Z_lt_dec j cursor) as [Hlt | Hnlt].
    + rewrite Znth_app_left__feasible_size_init.
      * apply Hvalues. lia.
      * lia.
    + assert (j = cursor) by lia.
      subst j.
      rewrite <- Hlength.
      apply Znth_app_last__feasible_size_init.
Qed.
Lemma cut_scan_initial_addition_bound__feasible_size_init :
  forall n k edges parent_data order_data sizes,
    Pre n k edges ->
    RootedOrderModel n edges parent_data order_data ->
    Zlength sizes = n ->
    (forall vertex, 0 <= vertex < n -> Znth vertex sizes 0 = 1) ->
    (forall j, 0 <= j < n ->
      ((0 <= Znth j order_data 0 < n /\
        -1 <= Znth j parent_data 0) /\
       Znth j parent_data 0 < n)) ->
    (0 <= n - 1 ->
      let vertex := Znth (n - 1) order_data 0 in
      Znth vertex parent_data (-1) >= 0 ->
      Znth (Znth vertex parent_data (-1)) sizes 0 +
        Znth vertex sizes 0 <= n).
Proof.
  intros n k edges parent_data order_data sizes Hpre Hroot
    Hlength Hones Harray_bounds Hcursor.
  cbn.
  intros Hparent_nonnegative.
  assert (Hn : 2 <= n).
  { unfold Pre in Hpre. intuition lia. }
  pose proof (Harray_bounds (n - 1) ltac:(lia)) as Hcursor_bounds.
  destruct Hcursor_bounds as [[[Hvertex_lo Hvertex_hi] _] _].
  pose proof
    (Harray_bounds (Znth (n - 1) order_data 0) ltac:(lia))
    as Hvertex_bounds.
  destruct Hvertex_bounds as [[_ _] Hparent_hi].
  unfold RootedOrderModel in Hroot.
  destruct Hroot as [_ [Hparent_length _]].
  rewrite <- (Znth_indep parent_data
    (Znth (n - 1) order_data 0) (-1) 0) in Hparent_hi by lia.
  rewrite Hones by lia.
  rewrite Hones by lia.
  lia.
Qed.
Lemma cut_scan_state_initial__feasible_size_init :
  forall n k edges minimum parent_data order_data sizes,
    Pre n k edges ->
    RootedOrderModel n edges parent_data order_data ->
    (forall j, 0 <= j < n ->
      ((0 <= Znth j order_data 0 < n /\
        -1 <= Znth j parent_data 0) /\
       Znth j parent_data 0 < n)) ->
    1 <= minimum <= n ->
    Zlength sizes = n ->
    (forall vertex, 0 <= vertex < n -> Znth vertex sizes 0 = 1) ->
    CutScanState n k edges minimum (n - 1) 0
      parent_data order_data sizes.
Proof.
  intros n k edges minimum parent_data order_data sizes Hpre Hroot
    Harray_bounds Hminimum Hlength Hones.
  assert (Hn : 1 <= n).
  { unfold Pre in Hpre. intuition lia. }
  assert (Hready : CutScanReady n k edges parent_data order_data).
  { unfold Pre in Hpre. intuition. }
  unfold CutScanReady in Hready.
  specialize (Hready minimum sizes Hminimum Hlength Hones).
  destruct Hready as
    [final_components [final_sizes
      [Hscan [Hcomponents [Hfinal_length [Hfinal_bounds Hthreshold]]]]]].
  pose proof Hroot as Hroot_model.
  unfold RootedOrderModel in Hroot.
  destruct Hroot as
    [Hroot_n [Hparent_length [Horder_length Hroot_rest]]].
  unfold CutScanState.
  split.
  - split; lia.
  - split.
    + split; lia.
    + split; [exact Hparent_length |].
      split; [exact Horder_length |].
      split; [exact Hroot_model |].
      split.
      * unfold CutScanNodeBounds.
        split; [exact Hlength |].
        split.
        -- intros vertex Hvertex.
           rewrite Hones by exact Hvertex.
           lia.
        -- eapply cut_scan_initial_addition_bound__feasible_size_init;
             eauto.
      * exists final_components, final_sizes.
        split; [exact Hscan |].
        split; [exact Hcomponents |].
        split; [exact Hfinal_length |].
        split; assumption.
Qed.
Lemma cut_scan_terminal_threshold__feasible_returns :
  forall n k edges minimum cursor components parent_data order_data sizes,
    cursor < 0 ->
    CutScanState n k edges minimum cursor components
      parent_data order_data sizes ->
    (components >= k + 1 <-> ThresholdFeasible n k edges minimum).
Proof.
  intros n k edges minimum cursor components parent_data order_data sizes
    Hcursor Hstate.
  unfold CutScanState in Hstate.
  destruct Hstate as
    [Hcursor_bounds [_ [_ [_ [_ [_
      [final_components [final_sizes
        [Hscan [_ [_ [_ Hthreshold]]]]]]]]]]]].
  assert (cursor = -1) by lia.
  subst cursor.
  inversion Hscan; subst; try lia.
  exact Hthreshold.
Qed.
Lemma Zlength_replace_Znth__solver_adjacency_build :
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
Lemma Znth_app_left__solver_adjacency_build :
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
Lemma Znth_app_last__solver_adjacency_build :
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
Lemma Znth_replace_same__solver_adjacency_build :
  forall (A : Type) (xs : list A) i v d,
    0 <= i < Zlength xs ->
    Znth i (replace_Znth i v xs) d = v.
Proof.
  intros A xs i v d Hi.
  apply Znth_replace_Znth_Same. exact Hi.
Qed.
Lemma Znth_replace_diff__solver_adjacency_build :
  forall (A : Type) (xs : list A) i j v d,
    0 <= i < Zlength xs ->
    0 <= j < Zlength xs -> i <> j ->
    Znth j (replace_Znth i v xs) d = Znth j xs d.
Proof.
  intros A xs i j v d Hi Hj Hneq.
  apply Znth_replace_Znth_Diff; assumption.
Qed.
Lemma adjacency_path_app_old__solver_adjacency_build :
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
      rewrite Znth_app_left__solver_adjacency_build in Hmiddle by
        (rewrite Hlen; exact Hfrom_old).
      exact Hmiddle. }
    assert (Hmiddle_old : middle = -1 \/ 0 <= middle < 2 * done).
    { specialize (Hslots start Hfrom_old).
      rewrite Znth_app_left__solver_adjacency_build in Hmiddle by
        (rewrite Hlen; exact Hfrom_old).
      destruct Hslots; [left | right]; lia. }
    exists middle. split; [exact Hstep_old |].
    apply (IH middle Hmiddle_old Htail).
Qed.
Lemma adjacency_path_old_app__solver_adjacency_build :
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
      * rewrite Znth_app_left__solver_adjacency_build by exact Hfrom.
        exact Hmiddle.
    + apply IH. exact Htail.
Qed.
Lemma adjacency_step_path__solver_adjacency_build :
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
Lemma adjacency_path_finish_bound__solver_adjacency_build :
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
Lemma adjacency_slot_push_iff__solver_adjacency_build :
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
  { unfold head1. rewrite Zlength_replace_Znth__solver_adjacency_build.
    exact Hhead. }
  assert (Hhead2 : Zlength head2 = n).
  { unfold head2. rewrite Zlength_replace_Znth__solver_adjacency_build.
    exact Hhead1. }
  assert (Hnext2 : Zlength next2 = 2 * done + 2).
  { unfold next2. repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
    rewrite Zlength_nil, Hnext. lia. }
  assert (Hhead1_v : Znth v head1 (-1) = Znth v head_data (-1)).
  { unfold head1. apply Znth_replace_diff__solver_adjacency_build;
      rewrite ?Hhead; lia. }
  assert (Hhead2_u : Znth u head2 (-1) = 2 * done).
  { unfold head2, head1.
    rewrite Znth_replace_diff__solver_adjacency_build by
      (rewrite ?Zlength_replace_Znth__solver_adjacency_build, ?Hhead; lia).
    apply Znth_replace_same__solver_adjacency_build. rewrite Hhead. lia. }
  assert (Hhead2_v : Znth v head2 (-1) = 2 * done + 1).
  { unfold head2. apply Znth_replace_same__solver_adjacency_build.
    rewrite Hhead1. lia. }
  assert (Hhead2_other : forall y, 0 <= y < n -> y <> u -> y <> v ->
      Znth y head2 (-1) = Znth y head_data (-1)).
  { intros y Hy Hyu Hyv. unfold head2, head1.
    rewrite Znth_replace_diff__solver_adjacency_build by
      (rewrite ?Zlength_replace_Znth__solver_adjacency_build, ?Hhead; lia).
    apply Znth_replace_diff__solver_adjacency_build; rewrite ?Hhead; lia. }
  assert (Hnext_u : AdjacencyNext next2 (2 * done) (Znth u head_data (-1))).
  { split; [rewrite Hnext2; lia |]. unfold next2.
    replace (Znth u head_data (-1) :: Znth v head1 (-1) :: nil)
      with ((Znth u head_data (-1) :: nil) ++ Znth v head1 (-1) :: nil)
      by reflexivity.
    rewrite app_assoc.
    rewrite Znth_app_left__solver_adjacency_build by
      (repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
       rewrite Zlength_nil, Hnext; lia).
    replace (2 * done) with (Zlength next_data) by lia.
    symmetry. apply Znth_app_last__solver_adjacency_build. }
  assert (Hnext_v : AdjacencyNext next2 (2 * done + 1) (Znth v head_data (-1))).
  { split; [rewrite Hnext2; lia |]. unfold next2.
    replace (Znth u head_data (-1) :: Znth v head1 (-1) :: nil)
      with ((Znth u head_data (-1) :: nil) ++ Znth v head1 (-1) :: nil)
      by reflexivity.
    rewrite app_assoc.
    rewrite <- Hhead1_v.
    replace (2 * done + 1) with
      (Zlength (next_data ++ Znth u head_data (-1) :: nil)).
    - symmetry. apply Znth_app_last__solver_adjacency_build.
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
        { apply adjacency_path_app_old__solver_adjacency_build with
              (a := Znth u head_data (-1)) (b := Znth v head1 (-1))
              (done := done); try assumption.
          unfold clos_refl_trans; sets_unfold. exists steps. exact Htail. }
        assert (Hfinish := adjacency_path_finish_bound__solver_adjacency_build
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
           { apply adjacency_path_app_old__solver_adjacency_build with
                 (a := Znth u head_data (-1)) (b := Znth v head1 (-1))
                 (done := done); try assumption.
             unfold clos_refl_trans; sets_unfold. exists steps. exact Htail. }
           assert (Hfinish := adjacency_path_finish_bound__solver_adjacency_build
             next_data done (Znth v head_data (-1)) slot Hslots Hold_head Hreach_old).
           left. unfold AdjacencySlot.
           split; [rewrite Hhead; exact Hv |]. split; [lia | exact Hreach_old].
      * assert (Hold_head : Znth x head_data (-1) = -1 \/
                   0 <= Znth x head_data (-1) < 2 * done).
        { apply Hheads. exact Hxn. }
        rewrite Hhead2_other in Hpath by auto.
        assert (Hreach_old : clos_refl_trans (AdjacencyNext next_data)
            (Znth x head_data (-1)) slot).
        { apply adjacency_path_app_old__solver_adjacency_build with
            (a := Znth u head_data (-1)) (b := Znth v head1 (-1))
            (done := done); try assumption. }
        assert (Hfinish := adjacency_path_finish_bound__solver_adjacency_build
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
        apply adjacency_step_path__solver_adjacency_build with
          (y := Znth u head_data (-1)); [exact Hnext_u |].
        apply adjacency_path_old_app__solver_adjacency_build. exact Hpath.
      * destruct (Z.eq_dec x v) as [-> | Hxv].
        -- rewrite Hhead2_v.
           apply adjacency_step_path__solver_adjacency_build with
             (y := Znth v head_data (-1)); [exact Hnext_v |].
           apply adjacency_path_old_app__solver_adjacency_build. exact Hpath.
        -- rewrite Hhead2_other by auto.
           apply adjacency_path_old_app__solver_adjacency_build. exact Hpath.
    + unfold AdjacencySlot. split; [rewrite Hhead2; exact Hu |].
      split; [rewrite Hnext2; lia |]. rewrite Hhead2_u.
      unfold clos_refl_trans; sets_unfold. exists 0%nat. simpl. sets_unfold. reflexivity.
    + unfold AdjacencySlot. split; [rewrite Hhead2; exact Hv |].
      split; [rewrite Hnext2; lia |]. rewrite Hhead2_v.
      unfold clos_refl_trans; sets_unfold. exists 0%nat. simpl. sets_unfold. reflexivity.
Qed.
Lemma firstn_succ_Znth__solver_adjacency_build :
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
Lemma sublist_prefix_succ__solver_adjacency_build :
  forall (A : Type) (l : list A) i d,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l d :: nil.
Proof.
  intros A l i d Hi.
  unfold sublist. simpl.
  apply firstn_succ_Znth__solver_adjacency_build. exact Hi.
Qed.
Lemma Znth_app_two_first__solver_adjacency_build :
  forall (A : Type) (xs : list A) a b d,
    Znth (Zlength xs) (xs ++ a :: b :: nil) d = a.
Proof.
  intros A xs a b d.
  replace (a :: b :: nil) with ((a :: nil) ++ b :: nil) by reflexivity.
  rewrite app_assoc.
  rewrite Znth_app_left__solver_adjacency_build.
  - apply Znth_app_last__solver_adjacency_build.
  - repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
    rewrite Zlength_nil. pose proof (Zlength_nonneg xs). lia.
Qed.
Lemma Znth_app_two_second__solver_adjacency_build :
  forall (A : Type) (xs : list A) a b d,
    Znth (Zlength xs + 1) (xs ++ a :: b :: nil) d = b.
Proof.
  intros A xs a b d.
  replace (a :: b :: nil) with ((a :: nil) ++ b :: nil) by reflexivity.
  rewrite app_assoc.
  replace (Zlength xs + 1) with (Zlength (xs ++ a :: nil)).
  - apply Znth_app_last__solver_adjacency_build.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.
Lemma canonical_swap__solver_adjacency_build :
  forall u v, CanonicalEdge (u, v) = CanonicalEdge (v, u).
Proof.
  intros u v. unfold CanonicalEdge. simpl.
  rewrite Z.min_comm, Z.max_comm. reflexivity.
Qed.
Lemma adjacency_build_extend__solver_adjacency_build :
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
  { unfold head1. rewrite Zlength_replace_Znth__solver_adjacency_build. exact Hhead. }
  assert (Hhead2 : Zlength head2 = n).
  { unfold head2. rewrite Zlength_replace_Znth__solver_adjacency_build. exact Hhead1. }
  assert (Hto2 : Zlength to2 = 2 * i + 2).
  { unfold to2. repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
    rewrite Zlength_nil, Hto. lia. }
  assert (Hnext2 : Zlength next2 = 2 * i + 2).
  { unfold next2. repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
    rewrite Zlength_nil, Hnext. lia. }
  assert (Hhead1_v : Znth v head1 (-1) = Znth v head_data (-1)).
  { unfold head1. apply Znth_replace_diff__solver_adjacency_build;
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
    apply (adjacency_slot_push_iff__solver_adjacency_build
      n i head_data next_data u v); try assumption; lia. }
  assert (Hno_old_edge :
      ~ (In (u + 1, v + 1) (sublist 0 i edges) \/
         In (v + 1, u + 1) (sublist 0 i edges))).
  { intros [Hin | Hin]; apply Hnot.
    - apply in_map. exact Hin.
    - pose proof (in_map CanonicalEdge (sublist 0 i edges)
        (v + 1, u + 1) Hin) as Hmapped.
      rewrite canonical_swap__solver_adjacency_build in Hmapped. exact Hmapped. }
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
      rewrite Znth_replace_diff__solver_adjacency_build by
        (rewrite ?Zlength_replace_Znth__solver_adjacency_build, ?Hhead; lia).
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
      * unfold to2. rewrite Znth_app_left__solver_adjacency_build by (rewrite Hto; lia).
        exact Hto_bounds.
      * unfold next2. rewrite Znth_app_left__solver_adjacency_build by (rewrite Hnext; lia).
        exact Hnext_bound.
    + assert (slot0 = 2 * i \/ slot0 = 2 * i + 1) by lia.
      destruct H as [-> | ->].
      * split.
        -- unfold to2. replace (2 * i) with (Zlength to_data) by lia.
           rewrite Znth_app_two_first__solver_adjacency_build. exact Hv.
        -- unfold next2. replace (2 * i) with (Zlength next_data) by lia.
           rewrite Znth_app_two_first__solver_adjacency_build.
           specialize (Hheads u Hu). destruct Hheads; [left | right]; lia.
      * split.
        -- unfold to2. replace (2 * i + 1) with (Zlength to_data + 1) by lia.
           rewrite Znth_app_two_second__solver_adjacency_build. exact Hu.
        -- unfold next2. replace (2 * i + 1) with (Zlength next_data + 1) by lia.
           rewrite Znth_app_two_second__solver_adjacency_build, Hhead1_v.
           specialize (Hheads v Hv). destruct Hheads; [left | right]; lia.
  - intros x y Hx Hy.
    rewrite sublist_prefix_succ__solver_adjacency_build with (d := d) by exact Hi.
    rewrite Hedge_i. repeat rewrite in_app_iff. simpl.
    split.
    + intros [[Hold | [Hxy | Hfalse]] | [Hold | [Hyx | Hfalse]]]; try contradiction.
      * destruct (proj1 (Hedge_model x y Hx Hy) (or_introl Hold))
          as [slot [Hslot Hval]].
        exists slot. split; [apply Hslot_iff; left; exact Hslot |].
        unfold to2. rewrite Znth_app_left__solver_adjacency_build by (rewrite Hto; destruct Hslot as [_ [Hb _]]; lia).
        exact Hval.
      * injection Hxy as Hxq Hyq.
        assert (x = u) by lia. assert (y = v) by lia. subst x y.
        exists (2 * i). split.
        -- apply Hslot_iff. right. left. auto.
        -- unfold to2. replace (2 * i) with (Zlength to_data) by lia.
           apply Znth_app_two_first__solver_adjacency_build.
      * destruct (proj1 (Hedge_model x y Hx Hy) (or_intror Hold))
          as [slot [Hslot Hval]].
        exists slot. split; [apply Hslot_iff; left; exact Hslot |].
        unfold to2. rewrite Znth_app_left__solver_adjacency_build by (rewrite Hto; destruct Hslot as [_ [Hb _]]; lia).
        exact Hval.
      * injection Hyx as Hyq Hxq.
        assert (x = v) by lia. assert (y = u) by lia. subst x y.
        exists (2 * i + 1). split.
        -- apply Hslot_iff. right. right. auto.
        -- unfold to2. replace (2 * i + 1) with (Zlength to_data + 1) by lia.
           apply Znth_app_two_second__solver_adjacency_build.
    + intros [slot [Hslot Hval]]. apply Hslot_iff in Hslot.
      destruct Hslot as [Holdslot | [[-> ->] | [-> ->]]].
      * pose proof (proj2 (Hedge_model x y Hx Hy)) as Hold_edge.
        assert (Hedge_old : In (x + 1, y + 1) (sublist 0 i edges) \/
            In (y + 1, x + 1) (sublist 0 i edges)).
        { apply Hold_edge. exists slot. split; [exact Holdslot |].
        unfold to2 in Hval. rewrite Znth_app_left__solver_adjacency_build in Hval
          by (rewrite Hto; destruct Holdslot as [_ [Hb _]]; lia).
          exact Hval. }
        destruct Hedge_old as [Hedge_old | Hedge_old].
        -- left. left. exact Hedge_old.
        -- right. left. exact Hedge_old.
      * unfold to2 in Hval. replace (2 * i) with (Zlength to_data) in Hval by lia.
        rewrite Znth_app_two_first__solver_adjacency_build in Hval. subst y.
        left. right. auto.
      * unfold to2 in Hval. replace (2 * i + 1) with (Zlength to_data + 1) in Hval by lia.
        rewrite Znth_app_two_second__solver_adjacency_build in Hval. subst y.
        right. right. auto.
  - intros x slot1 slot2 Hs1 Hs2 Hval.
    rewrite Hslot_iff in Hs1, Hs2.
    destruct Hs1 as [Hold1 | [[Hx1 Hslot1] | [Hx1 Hslot1]]];
    destruct Hs2 as [Hold2 | [[Hx2 Hslot2] | [Hx2 Hslot2]]].
    + apply (Hunique x slot1 slot2 Hold1 Hold2).
      unfold to2 in Hval.
      rewrite !Znth_app_left__solver_adjacency_build in Hval
        by (destruct Hold1 as [_ [Hb1 _]]; destruct Hold2 as [_ [Hb2 _]];
            rewrite Hnext in Hb1, Hb2; rewrite Hto; lia).
      exact Hval.
    + subst x slot2. exfalso. apply Hno_old_edge.
      apply (proj2 (Hedge_model u v Hu Hv)). exists slot1. split; [exact Hold1 |].
      unfold to2 in Hval. rewrite Znth_app_left__solver_adjacency_build in Hval at 1
        by (destruct Hold1 as [_ [Hb _]]; rewrite Hto, <- Hnext; exact Hb).
      replace (2 * i) with (Zlength to_data) in Hval by lia.
      rewrite Znth_app_two_first__solver_adjacency_build in Hval. exact Hval.
    + subst x slot2. exfalso. apply Hno_old_edge.
      assert (Hedge_vu : In (v + 1, u + 1) (sublist 0 i edges) \/
          In (u + 1, v + 1) (sublist 0 i edges)).
      { apply (proj2 (Hedge_model v u Hv Hu)). exists slot1. split; [exact Hold1 |].
        unfold to2 in Hval. rewrite Znth_app_left__solver_adjacency_build in Hval at 1
          by (destruct Hold1 as [_ [Hb _]]; rewrite Hto, <- Hnext; exact Hb).
        replace (2 * i + 1) with (Zlength to_data + 1) in Hval by lia.
        rewrite Znth_app_two_second__solver_adjacency_build in Hval. exact Hval. }
      destruct Hedge_vu; auto.
    + subst x slot1. exfalso. apply Hno_old_edge.
      apply (proj2 (Hedge_model u v Hu Hv)). exists slot2. split; [exact Hold2 |].
      symmetry in Hval. unfold to2 in Hval.
      rewrite Znth_app_left__solver_adjacency_build in Hval at 1
        by (destruct Hold2 as [_ [Hb _]]; rewrite Hto, <- Hnext; exact Hb).
      replace (2 * i) with (Zlength to_data) in Hval by lia.
      rewrite Znth_app_two_first__solver_adjacency_build in Hval. exact Hval.
    + congruence.
    + subst x slot1. subst slot2. exfalso. apply Huv. lia.
    + subst x slot1. exfalso. apply Hno_old_edge.
      assert (Hedge_vu : In (v + 1, u + 1) (sublist 0 i edges) \/
          In (u + 1, v + 1) (sublist 0 i edges)).
      { apply (proj2 (Hedge_model v u Hv Hu)). exists slot2. split; [exact Hold2 |].
        symmetry in Hval. unfold to2 in Hval.
        rewrite Znth_app_left__solver_adjacency_build in Hval at 1
          by (destruct Hold2 as [_ [Hb _]]; rewrite Hto, <- Hnext; exact Hb).
        replace (2 * i + 1) with (Zlength to_data + 1) in Hval by lia.
        rewrite Znth_app_two_second__solver_adjacency_build in Hval. exact Hval. }
      destruct Hedge_vu; auto.
    + subst x slot1. subst slot2. exfalso. apply Huv. lia.
    + congruence.
Qed.
Lemma adjacency_build_empty__solver_adjacency_build :
  forall n edges head_data,
    0 <= n ->
    Zlength head_data = n ->
    (forall u, 0 <= u < n -> Znth u head_data (-1) = -1) ->
    AdjacencyBuildState n edges 0 head_data nil nil.
Proof.
  intros n edges head_data Hn Hhead Hvalues.
  unfold AdjacencyBuildState.
  split; [pose proof (Zlength_nonneg edges); lia |].
  split; [exact Hhead |].
  split; [rewrite Zlength_nil; lia |].
  split; [rewrite Zlength_nil; lia |].
  split.
  - intros u Hu. left. apply Hvalues. exact Hu.
  - split.
    + intros slot Hslot. lia.
    + split.
      * intros u v Hu Hv. split.
        -- unfold sublist. simpl. tauto.
        -- intros [slot [Hslot Hto]].
           unfold AdjacencySlot in Hslot.
           destruct Hslot as [_ [Hbound _]]. rewrite Zlength_nil in Hbound. lia.
      * intros u slot1 slot2 Hslot1.
        unfold AdjacencySlot in Hslot1.
        destruct Hslot1 as [_ [Hbound _]]. rewrite Zlength_nil in Hbound. lia.
Qed.
Lemma adjacency_build_complete__solver_adjacency_build :
  forall n edges head_data to_data next_data,
    Zlength edges = n - 1 ->
    AdjacencyBuildState n edges (n - 1)
      head_data to_data next_data ->
    AdjacencyModel n edges head_data to_data next_data.
Proof.
  intros n edges head_data to_data next_data Hedges Hbuild.
  unfold AdjacencyBuildState in Hbuild.
  destruct Hbuild as
    [Hdone [Hhead [Hto [Hnext [Hheads [Hslots [Hedge_model Hunique]]]]]]].
  unfold AdjacencyModel.
  repeat split; try lia; try assumption.
  - intros u Hu.
    specialize (Hheads u Hu).
    replace (2 * n - 2) with (2 * (n - 1)) by lia.
    exact Hheads.
  - pose proof (Hslots slot ltac:(lia)) as [Hto_bounds Hnext_bound].
    lia.
  - pose proof (Hslots slot ltac:(lia)) as [Hto_bounds Hnext_bound].
    lia.
  - pose proof (Hslots slot ltac:(lia)) as [Hto_bounds Hnext_bound].
    exact Hnext_bound.
  - rewrite (sublist_self edges (n - 1)) in Hedge_model by
      (symmetry; exact Hedges).
    exact (proj1 (Hedge_model u v H H0)).
  - rewrite (sublist_self edges (n - 1)) in Hedge_model by
      (symmetry; exact Hedges).
    exact (proj2 (Hedge_model u v H H0)).
Qed.
Lemma bounded_nodup_complete__solver_traversal_init :
  forall n (order_data : list Z),
    0 <= n ->
    Zlength order_data = n ->
    NoDup order_data ->
    (forall q, 0 <= q < Zlength order_data ->
      0 <= Znth q order_data 0 < n) ->
    forall vertex, 0 <= vertex < n -> In vertex order_data.
Proof.
  intros n order_data Hn Hlength Hnodup Hbounds.
  set (vertices := map Z.of_nat (seq 0 (Z.to_nat n))).
  assert (Hincl : incl order_data vertices).
  { intros vertex Hin.
    destruct (In_nth order_data vertex 0 Hin) as [q [Hq Hvertex]].
    assert (Hqz : 0 <= Z.of_nat q < Zlength order_data).
    { rewrite Zlength_correct. lia. }
    specialize (Hbounds (Z.of_nat q) Hqz).
    unfold Znth in Hbounds.
    rewrite Nat2Z.id in Hbounds.
    rewrite Hvertex in Hbounds.
    unfold vertices.
    apply in_map_iff.
    exists (Z.to_nat vertex).
    split; [lia |].
    apply in_seq.
    lia. }
  assert (Hvertices_length : (length vertices <= length order_data)%nat).
  { unfold vertices.
    rewrite map_length, seq_length.
    rewrite Zlength_correct in Hlength.
    lia. }
  pose proof (NoDup_length_incl Hnodup Hvertices_length Hincl) as Hreverse.
  intros vertex Hvertex.
  apply Hreverse.
  unfold vertices.
  apply in_map_iff.
  exists (Z.to_nat vertex).
  split; [lia |].
  apply in_seq.
  lia.
Qed.
Lemma adjacency_from_minus_one__solver_traversal_init :
  forall head_data next_data vertex slot,
    Znth vertex head_data (-1) = -1 ->
    AdjacencySlot head_data next_data vertex slot ->
    False.
Proof.
  intros head_data next_data vertex slot Hhead Hslot.
  unfold AdjacencySlot in Hslot.
  destruct Hslot as [_ [Hslot_bounds Hreach]].
  rewrite Hhead in Hreach.
  unfold clos_refl_trans in Hreach.
  sets_unfold in Hreach.
  destruct Hreach as [steps Hsteps].
  revert Hsteps.
  induction steps as [|steps IH]; intros Hsteps.
  - simpl in Hsteps. sets_unfold in Hsteps. lia.
  - simpl in Hsteps. sets_unfold in Hsteps.
    destruct Hsteps as [middle [Hnext _]].
    unfold AdjacencyNext in Hnext.
    lia.
Qed.
Lemma adjacency_refl__solver_traversal_init :
  forall head_data next_data vertex cursor,
    0 <= vertex < Zlength head_data ->
    0 <= cursor < Zlength next_data ->
    cursor = Znth vertex head_data (-1) ->
    AdjacencySlot head_data next_data vertex cursor.
Proof.
  intros head_data next_data vertex cursor Hvertex Hcursor ->.
  unfold AdjacencySlot.
  split; [exact Hvertex |].
  split; [exact Hcursor |].
  unfold clos_refl_trans.
  sets_unfold.
  exists O.
  simpl.
  sets_unfold.
  reflexivity.
Qed.
Lemma traversal_adj_enter__solver_traversal_init :
  forall n k edges processed order_data parent_cells
      head_data to_data next_data vertex parent_vertex,
    Pre n k edges ->
    AdjacencyModel n edges head_data to_data next_data ->
    TraversalEntryState n edges processed order_data parent_cells ->
    processed < Zlength order_data ->
    vertex = Znth processed order_data 0 ->
    Znth vertex parent_cells None = Some parent_vertex ->
    TraversalAdjState n edges processed order_data parent_cells
      head_data to_data next_data vertex parent_vertex
      (Znth vertex head_data (-1)).
Proof.
  intros n k edges processed order_data parent_cells
    head_data to_data next_data vertex parent_vertex
    Hpre Hadj Hentry_state Hactive Hvertex Hparent.
  pose proof Hpre as Hpre_bounds.
  unfold Pre in Hpre_bounds.
  destruct Hpre_bounds as [_ [_ [_ [Hedge_bounds _]]]].
  rewrite Forall_forall in Hedge_bounds.
  assert (Hedge_vertices : forall a b,
      (In (a + 1, b + 1) edges \/ In (b + 1, a + 1) edges) ->
      0 <= a < n /\ 0 <= b < n).
  { intros a b Hedge.
    destruct Hedge as [Hedge | Hedge].
    - specialize (Hedge_bounds (a + 1, b + 1) Hedge).
      simpl in Hedge_bounds. lia.
    - specialize (Hedge_bounds (b + 1, a + 1) Hedge).
      simpl in Hedge_bounds. lia. }
  unfold AdjacencyModel in Hadj.
  destruct Hadj as
    [Hhead_length [Hto_length [Hnext_length [Hedges_length
     [Hheads [Hslots [Hedge_model Hunique]]]]]]].
  unfold TraversalEntryState in Hentry_state.
  destruct Hentry_state as [Htraversal Hentry].
  pose proof Htraversal as Htraversal_parts.
  unfold TraversalState in Htraversal_parts.
  destruct Htraversal_parts as
    [Hparent_length [Hprocessed_bounds [Horder_bounds [Hnodup [Hroot
     [Hvertices [Hprocessed_neighbors Hpending]]]]]]].
  specialize (Hentry Hactive).
  simpl in Hentry.
  destruct Hentry as [entry_parent [Hentry_parent Hfresh]].
  rewrite <- Hvertex in Hentry_parent.
  rewrite Hparent in Hentry_parent.
  injection Hentry_parent as Hentry_parent.
  subst entry_parent.
  rewrite <- Hvertex in Hfresh.
  assert (Hvertex_bounds : 0 <= vertex < n).
  { specialize (Hvertices processed ltac:(lia)).
    simpl in Hvertices.
    rewrite <- Hvertex in Hvertices.
    exact (proj1 Hvertices). }
  assert (Hcursor_shape :
      Znth vertex head_data (-1) = -1 \/
      0 <= Znth vertex head_data (-1) < 2 * n - 2).
  { apply Hheads. exact Hvertex_bounds. }
  assert (Hcursor_slot :
      Znth vertex head_data (-1) <> -1 ->
      AdjacencySlot head_data next_data vertex
        (Znth vertex head_data (-1))).
  { intros Hnotminus.
    apply adjacency_refl__solver_traversal_init.
    - lia.
    - rewrite Hnext_length. destruct Hcursor_shape; lia.
    - reflexivity. }
  assert (Hslot_edge : forall slot,
      AdjacencySlot head_data next_data vertex slot ->
      (In (vertex + 1, Znth slot to_data 0 + 1) edges \/
       In (Znth slot to_data 0 + 1, vertex + 1) edges)).
  { intros slot Hslot.
    pose proof Hslot as Hslot_copy.
    unfold AdjacencySlot in Hslot.
    destruct Hslot as [_ [Hslot_bounds Hreach]].
    specialize (Hslots slot ltac:(lia)).
    destruct Hslots as [Hneighbor_bounds _].
    apply (proj2 (Hedge_model vertex (Znth slot to_data 0)
      Hvertex_bounds Hneighbor_bounds)).
    exists slot. split.
    - exact Hslot_copy.
    - reflexivity. }
  assert (Horder_vertex_bounds : forall q,
      0 <= q < Zlength order_data ->
      0 <= Znth q order_data 0 < n).
  { intros q Hq.
    specialize (Hvertices q Hq).
    simpl in Hvertices.
    exact (proj1 Hvertices). }
  unfold TraversalAdjState.
  split; [exact Htraversal |].
  split.
  { destruct Hcursor_shape; lia. }
  split; [exact Hvertex_bounds |].
  split; [exact Hparent |].
  split.
  { destruct Hcursor_shape as [Hminus | Hrange].
    - left; exact Hminus.
    - right; apply Hcursor_slot; lia. }
  split.
  { intros slot Hslot Hscanned.
    destruct Hscanned as [Hminus | Hnot_reachable].
    - exfalso.
      eapply adjacency_from_minus_one__solver_traversal_init; eauto.
    - exfalso. apply Hnot_reachable.
      unfold AdjacencySlot in Hslot.
      exact (proj2 (proj2 Hslot)). }
  split.
  { intros slot Hslot Hreachable Hnot_parent.
    apply Hfresh.
    - apply Hslot_edge. exact Hslot.
    - exact Hnot_parent. }
  split.
  { intros Hnotminus.
    specialize (Hslots (Znth vertex head_data (-1)) ltac:(
      destruct Hcursor_shape; lia)).
    exact (proj1 Hslots). }
  split.
  { intros Hnotminus Hnot_parent.
    assert (Hslot : AdjacencySlot head_data next_data vertex
        (Znth vertex head_data (-1))) by
      (apply Hcursor_slot; exact Hnotminus).
    assert (Hnotin : ~ In
        (Znth (Znth vertex head_data (-1)) to_data 0) order_data).
    { apply Hfresh.
      - apply Hslot_edge. exact Hslot.
      - exact Hnot_parent. }
    split; [exact Hnotin |].
    destruct Horder_bounds as [_ Horder_upper].
    destruct (Z.eq_dec (Zlength order_data) n) as [Hequal | Hunequal].
    - exfalso. apply Hnotin.
      apply (bounded_nodup_complete__solver_traversal_init n order_data);
        try assumption; try lia.
      specialize (Hslots (Znth vertex head_data (-1)) ltac:(
        destruct Hcursor_shape; lia)).
      exact (proj1 Hslots).
    - lia. }
  intros Hminus neighbor Hedge.
  destruct (Hedge_vertices vertex neighbor Hedge) as [_ Hneighbor_bounds].
  specialize (Hedge_model vertex neighbor Hvertex_bounds Hneighbor_bounds).
  apply proj1 in Hedge_model.
  specialize (Hedge_model Hedge).
  destruct Hedge_model as [slot [Hslot _]].
  exfalso.
  eapply adjacency_from_minus_one__solver_traversal_init; eauto.
Qed.
Lemma root_traversal_entry__solver_traversal_init :
  forall n k edges,
    Pre n k edges ->
    TraversalEntryState n edges 0 (0 :: nil)
      (Some (-1) :: repeat None (Z.to_nat (n - 1))).
Proof.
  intros n k edges Hpre.
  pose proof Hpre as Hpre_parts.
  unfold Pre in Hpre_parts.
  destruct Hpre_parts as
    [Hkn [Hnmax [Hedges [Hedge_bounds
     [[Hloop_free Hnodup_edges] Hrest]]]]].
  assert (Hnpos : 0 < n) by lia.
  unfold TraversalEntryState.
  split.
  - unfold TraversalState.
    split.
    + rewrite Zlength_cons, Zlength_correct, repeat_length. lia.
    + split; [rewrite Zlength_cons, Zlength_nil; lia |].
      split; [rewrite Zlength_cons, Zlength_nil; lia |].
      split.
      * constructor; [simpl; tauto | constructor].
      * split; [reflexivity |].
        split.
        -- intros q Hq. rewrite Zlength_cons, Zlength_nil in Hq.
           assert (q = 0) by lia. subst q. simpl.
           rewrite !Znth0_cons.
           split; [split; lia |].
           exists (-1). split; [reflexivity |].
           left. lia.
        -- split.
           ++ intros q neighbor Hq. lia.
           ++ intros q neighbor parent_vertex Hq.
              rewrite Zlength_cons, Zlength_nil in Hq. lia.
  - intros Hactive. rewrite Zlength_cons, Zlength_nil in Hactive.
    exists (-1). split; [reflexivity |].
    intros neighbor Hedge Hnot_parent Hin.
    simpl in Hin. destruct Hin as [Hneighbor | Hin]; [|contradiction].
    subst neighbor.
    destruct Hedge as [Hedge | Hedge].
    + specialize (Hloop_free (1, 1) Hedge). simpl in Hloop_free. contradiction.
    + specialize (Hloop_free (1, 1) Hedge). simpl in Hloop_free. contradiction.
Qed.
Lemma adjacency_next_tail__solver_traversal_steps :
  forall next_data cursor slot,
    clos_refl_trans (AdjacencyNext next_data) cursor slot ->
    cursor <> slot ->
    clos_refl_trans (AdjacencyNext next_data)
      (Znth cursor next_data (-1)) slot.
Proof.
  intros next_data cursor slot Hreach Hneq.
  unfold clos_refl_trans in Hreach |- *.
  sets_unfold in Hreach. sets_unfold.
  destruct Hreach as [steps Hsteps].
  destruct steps as [|steps].
  - simpl in Hsteps. sets_unfold in Hsteps. subst slot. contradiction.
  - simpl in Hsteps. sets_unfold in Hsteps.
    destruct Hsteps as [middle [Hnext Htail]].
    unfold AdjacencyNext in Hnext.
    destruct Hnext as [_ Hmiddle]. subst middle.
    exists steps. exact Htail.
Qed.
Lemma Znth_default_irrelevant__solver_traversal_steps :
  forall (A : Type) (values : list A) i (d1 d2 : A),
    0 <= i < Zlength values ->
    Znth i values d1 = Znth i values d2.
Proof.
  intros A values i d1 d2 Hi. unfold Znth.
  apply nth_indep. apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. lia.
Qed.
Lemma adjacency_next_cons_early__solver_traversal_steps :
  forall next_data cursor slot,
    0 <= cursor < Zlength next_data ->
    clos_refl_trans (AdjacencyNext next_data)
      (Znth cursor next_data (-1)) slot ->
    clos_refl_trans (AdjacencyNext next_data) cursor slot.
Proof.
  intros next_data cursor slot Hcursor Hreach.
  unfold clos_refl_trans in Hreach |- *.
  sets_unfold in Hreach. sets_unfold.
  destruct Hreach as [steps Hsteps].
  exists (S steps). simpl. sets_unfold.
  exists (Znth cursor next_data (-1)). split.
  - unfold AdjacencyNext. split; [exact Hcursor | reflexivity].
  - exact Hsteps.
Qed.
Lemma adjacency_slot_next_early__solver_traversal_steps :
  forall head_data next_data vertex cursor,
    AdjacencySlot head_data next_data vertex cursor ->
    0 <= Znth cursor next_data (-1) < Zlength next_data ->
    AdjacencySlot head_data next_data vertex
      (Znth cursor next_data (-1)).
Proof.
  intros head_data next_data vertex cursor Hslot Hnextbounds.
  unfold AdjacencySlot in Hslot |- *.
  destruct Hslot as [Hvertex [Hcursor Hreach]].
  split; [exact Hvertex |]. split; [exact Hnextbounds |].
  etransitivity; [exact Hreach |].
  unfold clos_refl_trans. sets_unfold.
  exists 1%nat. simpl. sets_unfold.
  exists (Znth cursor next_data (-1)). split.
  - unfold AdjacencyNext. split; [exact Hcursor | reflexivity].
  - reflexivity.
Qed.
Lemma traversal_parent_in_order__solver_traversal_steps :
  forall n edges processed order_data parent_cells vertex parent_vertex,
    TraversalState n edges processed order_data parent_cells ->
    processed < Zlength order_data ->
    vertex = Znth processed order_data 0 ->
    Znth vertex parent_cells None = Some parent_vertex ->
    0 <= parent_vertex ->
    In parent_vertex order_data.
Proof.
  intros n edges processed order_data parent_cells vertex parent_vertex
    Htrav Hprocessed Hvertex Hparent Hparent_nonneg.
  unfold TraversalState in Htrav.
  destruct Htrav as [_ [Hproc [_ [_ [_ [Hvertices _]]]]]].
  specialize (Hvertices processed ltac:(lia)). simpl in Hvertices.
  rewrite <- Hvertex in Hvertices.
  destruct Hvertices as [_ [pv [Hpv Hshape]]].
  rewrite Hparent in Hpv. injection Hpv as Hpv. subst pv.
  destruct Hshape as [[Hroot Hminus] |
    [parent_pos [Hpos [Hpveq Hedge]]]].
  - lia.
  - rewrite Hpveq. unfold Znth. apply nth_In.
    apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
Qed.
Lemma pre_edge_bounds__solver_traversal_steps :
  forall n k edges u v,
    Pre n k edges ->
    (In (u + 1, v + 1) edges \/ In (v + 1, u + 1) edges) ->
    0 <= u < n /\ 0 <= v < n.
Proof.
  intros n k edges u v Hpre Hedge.
  unfold Pre in Hpre.
  destruct Hpre as [_ [_ [_ [Hbounds _]]]].
  rewrite Forall_forall in Hbounds.
  destruct Hedge as [Hedge | Hedge].
  - specialize (Hbounds (u + 1, v + 1) Hedge). simpl in Hbounds. lia.
  - specialize (Hbounds (v + 1, u + 1) Hedge). simpl in Hbounds. lia.
Qed.
Lemma adjacency_slot_edge__solver_traversal_steps :
  forall n edges head_data to_data next_data vertex slot,
    AdjacencyModel n edges head_data to_data next_data ->
    0 <= vertex < n ->
    AdjacencySlot head_data next_data vertex slot ->
    (In (vertex + 1, Znth slot to_data 0 + 1) edges \/
     In (Znth slot to_data 0 + 1, vertex + 1) edges).
Proof.
  intros n edges head_data to_data next_data vertex slot
    Hmodel Hvertex Hslot.
  unfold AdjacencyModel in Hmodel.
  destruct Hmodel as [_ [_ [Hnext_length [_ [_ [Hslotbounds [Hedges _]]]]]]].
  pose proof Hslot as Hslot_copy.
  unfold AdjacencySlot in Hslot.
  destruct Hslot as [_ [Hslot_range Hreach]].
  specialize (Hslotbounds slot ltac:(rewrite <- Hnext_length; exact Hslot_range)).
  destruct Hslotbounds as [Hneighbor _].
  apply (proj2 (Hedges vertex (Znth slot to_data 0)
    Hvertex Hneighbor)).
  exists slot. split.
  - exact Hslot_copy.
  - reflexivity.
Qed.
Lemma bounded_nodup_length_early__solver_traversal_steps :
  forall n (values : list Z),
    0 <= n -> NoDup values ->
    (forall x, In x values -> 0 <= x < n) ->
    Zlength values <= n.
Proof.
  intros n values Hn Hnodup Hbounds.
  assert (Hincl : incl values (map Z.of_nat (seq 0 (Z.to_nat n)))).
  { intros x Hx. specialize (Hbounds x Hx).
    apply in_map_iff. exists (Z.to_nat x). split; [lia |].
    apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlength.
  rewrite map_length, seq_length in Hlength.
  rewrite Zlength_correct. lia.
Qed.
Lemma traversal_missing_length_lt__solver_traversal_steps :
  forall n edges processed order_data parent_cells fresh,
    TraversalState n edges processed order_data parent_cells ->
    0 <= fresh < n ->
    ~ In fresh order_data ->
    Zlength order_data < n.
Proof.
  intros n edges processed order_data parent_cells fresh
    Htrav Hfresh_bounds Hfresh_notin.
  unfold TraversalState in Htrav.
  destruct Htrav as [_ [_ [_ [Hnodup [_ [Hvertices _]]]]]].
  assert (Hall : forall x, In x (fresh :: order_data) -> 0 <= x < n).
  { intros x [Hx | Hx].
    - subst x. exact Hfresh_bounds.
    - destruct (In_nth order_data x 0 Hx) as [idx [Hidx Heq]].
      specialize (Hvertices (Z.of_nat idx)). simpl in Hvertices.
      assert (Hidxz : 0 <= Z.of_nat idx < Zlength order_data).
      { rewrite Zlength_correct. lia. }
      specialize (Hvertices Hidxz).
      unfold Znth in Hvertices. rewrite Nat2Z.id in Hvertices.
      rewrite Heq in Hvertices. exact (proj1 Hvertices). }
  assert (Hnodup_cons : NoDup (fresh :: order_data)).
  { constructor; assumption. }
  pose proof (bounded_nodup_length_early__solver_traversal_steps
    n (fresh :: order_data) ltac:(lia) Hnodup_cons Hall) as Hlength.
  rewrite Zlength_cons in Hlength. lia.
Qed.
Lemma traversal_adj_advance_parent__solver_traversal_steps :
  forall n k edges processed order_data parent_cells
    head_data to_data next_data vertex parent_vertex cursor,
    Pre n k edges ->
    AdjacencyModel n edges head_data to_data next_data ->
    processed < Zlength order_data ->
    vertex = Znth processed order_data 0 ->
    cursor <> -1 ->
    Znth cursor to_data 0 = parent_vertex ->
    TraversalAdjState n edges processed order_data parent_cells
      head_data to_data next_data vertex parent_vertex cursor ->
    TraversalAdjState n edges processed order_data parent_cells
      head_data to_data next_data vertex parent_vertex
      (Znth cursor next_data (-1)).
Proof.
  intros n k edges processed order_data parent_cells head_data to_data
    next_data vertex parent_vertex cursor Hpre Hmodel Hprocessed Hvertex
    Hcursor_nonterm Hto_parent Hadj.
  unfold TraversalAdjState in Hadj |- *.
  destruct Hadj as
    [Htrav [Hcursor_bounds [Hvertex_bounds [Hparent [Hslot
     [Hscanned [Hfresh [Hcurrent_bounds [Hcurrent_fresh Hdone]]]]]]]]].
  assert (Hcursor_range : 0 <= cursor < Zlength next_data).
  { unfold AdjacencyModel in Hmodel.
    destruct Hmodel as [_ [_ [Hnext_length _]]].
    rewrite Hnext_length. lia. }
  assert (Hnext_bounds :
    -1 <= Znth cursor next_data (-1) < 2 * n - 2).
  { unfold AdjacencyModel in Hmodel.
    destruct Hmodel as [_ [_ [_ [_ [_ [Hslots _]]]]]].
    specialize (Hslots cursor ltac:(lia)). lia. }
  assert (Hnext_range :
    Znth cursor next_data (-1) <> -1 ->
    0 <= Znth cursor next_data (-1) < Zlength next_data).
  { intros Hnext_nonterm.
    unfold AdjacencyModel in Hmodel.
    destruct Hmodel as [_ [_ [Hnext_length _]]].
    rewrite Hnext_length. lia. }
  assert (Hparent_bounds : 0 <= parent_vertex < n).
  { rewrite <- Hto_parent. apply Hcurrent_bounds. exact Hcursor_nonterm. }
  assert (Hparent_in : In parent_vertex order_data).
  { eapply traversal_parent_in_order__solver_traversal_steps.
    - exact Htrav.
    - exact Hprocessed.
    - exact Hvertex.
    - exact Hparent.
    - lia. }
  assert (Hcursor_slot : AdjacencySlot head_data next_data vertex cursor).
  { destruct Hslot as [Hterm | Hslot]; [contradiction | exact Hslot]. }
  split; [exact Htrav |].
  split; [exact Hnext_bounds |].
  split; [exact Hvertex_bounds |].
  split; [exact Hparent |].
  split.
  - destruct (Z.eq_dec (Znth cursor next_data (-1)) (-1)) as [Heq | Hneq].
    + left. exact Heq.
    + right. apply adjacency_slot_next_early__solver_traversal_steps;
        [exact Hcursor_slot | apply Hnext_range; exact Hneq].
  - split.
    + intros slot Hslot' Hbefore.
      destruct Hbefore as [Hnext_term | Hnotreach].
      * destruct (Z.eq_dec slot cursor) as [-> | Hneqslot].
        -- rewrite Hto_parent. exact Hparent_in.
        -- apply Hscanned; [exact Hslot' |]. right. intro Hreach.
           pose proof (adjacency_next_tail__solver_traversal_steps
             next_data cursor slot Hreach ltac:(congruence)) as Htail.
           rewrite Hnext_term in Htail.
           pose proof Hslot' as Hslot_bounds_copy.
           unfold AdjacencySlot in Hslot_bounds_copy.
           destruct Hslot_bounds_copy as [_ [Hslot_range _]].
           unfold clos_refl_trans in Htail. sets_unfold in Htail.
           destruct Htail as [steps Hsteps].
           destruct steps as [|steps].
           ++ simpl in Hsteps. sets_unfold in Hsteps. subst slot. lia.
           ++ simpl in Hsteps. sets_unfold in Hsteps.
              destruct Hsteps as [middle [Hfirst Hrest]].
              unfold AdjacencyNext in Hfirst. lia.
      * destruct (Z.eq_dec slot cursor) as [-> | Hneqslot].
        -- rewrite Hto_parent. exact Hparent_in.
        -- apply Hscanned; [exact Hslot' |]. right. intro Hreach.
           apply Hnotreach.
           apply (adjacency_next_tail__solver_traversal_steps
             next_data cursor slot Hreach ltac:(congruence)).
    + split.
      * intros slot Hslot' Hreach Hneq.
        apply (Hfresh slot Hslot').
        -- apply adjacency_next_cons_early__solver_traversal_steps;
             [exact Hcursor_range | exact Hreach].
        -- exact Hneq.
      * split.
        -- intros Hnext_nonterm.
           unfold AdjacencyModel in Hmodel.
           destruct Hmodel as [_ [_ [_ [_ [_ [Hslots _]]]]]].
           specialize (Hslots (Znth cursor next_data (-1)) ltac:(lia)).
           exact (proj1 Hslots).
        -- split.
           ++ intros Hnext_nonterm Hnext_notparent.
              split.
              ** apply (Hfresh (Znth cursor next_data (-1))).
                 --- apply adjacency_slot_next_early__solver_traversal_steps;
                       [exact Hcursor_slot | apply Hnext_range;
                         exact Hnext_nonterm].
                 --- apply adjacency_next_cons_early__solver_traversal_steps.
                     +++ exact Hcursor_range.
                     +++ unfold clos_refl_trans. sets_unfold.
                         exists 0%nat. simpl. sets_unfold. reflexivity.
                 --- exact Hnext_notparent.
              ** eapply traversal_missing_length_lt__solver_traversal_steps.
                 --- exact Htrav.
                 --- unfold AdjacencyModel in Hmodel.
                     destruct Hmodel as [_ [_ [_ [_ [_ [Hslots _]]]]]].
                     specialize (Hslots (Znth cursor next_data (-1))
                       ltac:(lia)). exact (proj1 Hslots).
                 --- apply (Hfresh (Znth cursor next_data (-1))).
                     +++ apply adjacency_slot_next_early__solver_traversal_steps;
                           [exact Hcursor_slot | apply Hnext_range;
                             exact Hnext_nonterm].
                     +++ apply adjacency_next_cons_early__solver_traversal_steps.
                         *** exact Hcursor_range.
                         *** unfold clos_refl_trans. sets_unfold.
                             exists 0%nat. simpl. sets_unfold. reflexivity.
                     +++ exact Hnext_notparent.
           ++ intros Hnext_term neighbor Hedge.
              pose proof (pre_edge_bounds__solver_traversal_steps
                n k edges vertex neighbor Hpre Hedge) as [_ Hneighbor_bounds].
              unfold AdjacencyModel in Hmodel.
              destruct Hmodel as [_ [_ [_ [_ [_ [_ [Hedges _]]]]]]].
              destruct (proj1 (Hedges vertex neighbor Hvertex_bounds Hneighbor_bounds)
                Hedge) as [slot [Hslot' Hto]].
              rewrite <- Hto.
              destruct (Z.eq_dec slot cursor) as [-> | Hneqslot].
              ** rewrite Hto_parent. exact Hparent_in.
              ** apply Hscanned; [exact Hslot' |]. right. intro Hreach.
                 pose proof (adjacency_next_tail__solver_traversal_steps
                   next_data cursor slot Hreach ltac:(congruence)) as Htail.
                 rewrite Hnext_term in Htail.
                 pose proof Hslot' as Hslot_bounds_copy.
                 unfold AdjacencySlot in Hslot_bounds_copy.
                 destruct Hslot_bounds_copy as [_ [Hslot_range _]].
                 unfold clos_refl_trans in Htail. sets_unfold in Htail.
                 destruct Htail as [steps Hsteps].
                 destruct steps as [|steps].
                 --- simpl in Hsteps. sets_unfold in Hsteps. subst slot. lia.
                 --- simpl in Hsteps. sets_unfold in Hsteps.
                     destruct Hsteps as [middle [Hfirst Hrest]].
                     unfold AdjacencyNext in Hfirst. lia.
Qed.
Lemma adjacency_next_cons__solver_traversal_steps :
  forall next_data cursor slot,
    0 <= cursor < Zlength next_data ->
    clos_refl_trans (AdjacencyNext next_data)
      (Znth cursor next_data (-1)) slot ->
    clos_refl_trans (AdjacencyNext next_data) cursor slot.
Proof.
  intros next_data cursor slot Hcursor Hreach.
  unfold clos_refl_trans in Hreach |- *.
  sets_unfold in Hreach. sets_unfold.
  destruct Hreach as [steps Hsteps].
  exists (S steps). simpl. sets_unfold.
  exists (Znth cursor next_data (-1)). split.
  - unfold AdjacencyNext. split; [exact Hcursor | reflexivity].
  - exact Hsteps.
Qed.
Lemma adjacency_slot_next__solver_traversal_steps :
  forall head_data next_data vertex cursor,
    AdjacencySlot head_data next_data vertex cursor ->
    0 <= Znth cursor next_data (-1) < Zlength next_data ->
    AdjacencySlot head_data next_data vertex
      (Znth cursor next_data (-1)).
Proof.
  intros head_data next_data vertex cursor Hslot Hnextbounds.
  unfold AdjacencySlot in Hslot |- *.
  destruct Hslot as [Hvertex [Hcursor Hreach]].
  split; [exact Hvertex |]. split; [exact Hnextbounds |].
  etransitivity; [exact Hreach |].
  unfold clos_refl_trans. sets_unfold.
  exists 1%nat. simpl. sets_unfold.
  exists (Znth cursor next_data (-1)). split.
  - unfold AdjacencyNext. split; [exact Hcursor | reflexivity].
  - reflexivity.
Qed.
Lemma bounded_nodup_length__solver_traversal_steps :
  forall n (values : list Z),
    0 <= n -> NoDup values ->
    (forall x, In x values -> 0 <= x < n) ->
    Zlength values <= n.
Proof.
  intros n values Hn Hnodup Hbounds.
  assert (Hincl : incl values (map Z.of_nat (seq 0 (Z.to_nat n)))).
  { intros x Hx. specialize (Hbounds x Hx).
    apply in_map_iff. exists (Z.to_nat x). split; [lia |].
    apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlength.
  rewrite map_length, seq_length in Hlength.
  rewrite Zlength_correct. lia.
Qed.
Lemma Zlength_replace_Znth__solver_traversal_steps :
  forall (A : Type) i (x : A) (values : list A),
    Zlength (replace_Znth i x values) = Zlength values.
Proof.
  intros A i x values. rewrite !Zlength_correct.
  unfold replace_Znth.
  assert (Hlength : forall m (vals : list A),
      length (replace_nth m vals x) = length vals).
  { intros m. induction m; intros vals; destruct vals; simpl;
      try reflexivity. rewrite IHm. reflexivity. }
  f_equal. apply Hlength.
Qed.
Lemma Znth_app_left__solver_traversal_steps :
  forall (A : Type) (d : A) (left right : list A) i,
    0 <= i < Zlength left ->
    Znth i (left ++ right) d = Znth i left d.
Proof.
  intros A d left. induction left as [|x left IH]; intros right i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Znth_app_last__solver_traversal_steps :
  forall (A : Type) (d x : A) (left : list A),
    Znth (Zlength left) (left ++ (x :: nil)) d = x.
Proof.
  intros A d x left. induction left as [|y left IH].
  - reflexivity.
  - simpl. rewrite Zlength_cons.
    rewrite Znth_cons by (pose proof (Zlength_nonneg left); lia).
    replace (Z.succ (Zlength left) - 1) with (Zlength left) by lia.
    exact IH.
Qed.
Lemma Znth_In__solver_traversal_finish :
  forall (A : Type) (l : list A) (d : A) i,
    0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l d i Hi. unfold Znth. apply nth_In.
  rewrite Zlength_correct in Hi. lia.
Qed.
Lemma In_Znth__solver_traversal_finish :
  forall (A : Type) (l : list A) (x d : A),
    In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  destruct (In_nth l x d Hin) as [i [Hi Heq]].
  exists (Z.of_nat i). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Heq.
Qed.
Lemma traversal_finish_entry__solver_traversal_steps :
  forall n edges processed order_data parent_cells
    head_data to_data next_data vertex parent_vertex,
    processed < Zlength order_data ->
    vertex = Znth processed order_data 0 ->
    TraversalAdjState n edges processed order_data parent_cells
      head_data to_data next_data vertex parent_vertex (-1) ->
    TraversalEntryState n edges (processed + 1) order_data parent_cells.
Proof.
  intros n edges processed order_data parent_cells head_data to_data next_data
    vertex parent_vertex Hprocessed Hvertex Hadj.
  unfold TraversalAdjState in Hadj.
  destruct Hadj as
    [Htrav [Hcursor [Hvbounds [Hparent [Hslot
     [Hscanned [Hfresh [Hcurbounds [Hcurfresh Hdone]]]]]]]]].
  unfold TraversalState in Htrav.
  destruct Htrav as
    [Hcells [Hproc_bounds [Hlen_bounds [Hnodup [Hroot
     [Hvertices [Hprocessed_neighbors Hpending]]]]]]].
  unfold TraversalEntryState. split.
  - unfold TraversalState.
    split; [exact Hcells |]. split; [lia |].
    split; [exact Hlen_bounds |]. split; [exact Hnodup |].
    split; [exact Hroot |]. split; [exact Hvertices |]. split.
    + intros q neighbor Hq Hedge.
      destruct (Z_lt_ge_dec q processed) as [Hlt | Hge].
      * apply (Hprocessed_neighbors q neighbor); lia || assumption.
      * assert (q = processed) by lia. subst q.
        apply Hdone; [reflexivity |]. rewrite Hvertex. exact Hedge.
    + intros q neighbor pv Hq Hcell Hedge Hneq.
      apply (Hpending q neighbor pv); try assumption; lia.
  - intros Hnext.
    specialize (Hvertices (processed + 1) ltac:(lia)). simpl in Hvertices.
    destruct Hvertices as [_ [pv [Hcell _]]].
    exists pv. split; [exact Hcell |].
    intros neighbor Hedge Hneq.
    apply (Hpending (processed + 1) neighbor pv); try assumption; lia.
Qed.
Lemma connected_prefix_of_traversal__solver_traversal_steps :
  forall n edges processed order_data parent_cells,
    TraversalState n edges processed order_data parent_cells ->
    ConnectedDiscoveryPrefix edges order_data.
Proof.
  intros n edges processed order_data parent_cells Htrav.
  unfold TraversalState in Htrav.
  destruct Htrav as [_ [_ [_ [_ [_ [Hvertices _]]]]]].
  unfold ConnectedDiscoveryPrefix.
  intros q Hq.
  specialize (Hvertices q ltac:(lia)). simpl in Hvertices.
  destruct Hvertices as [_ [parent_vertex [_ [Hroot | Hparent]]]].
  - lia.
  - destruct Hparent as [parent_pos [Hppos [Hpveq Hedge]]].
    exists parent_pos. split; [exact Hppos |].
    rewrite <- Hpveq. exact Hedge.
Qed.
Lemma nodup_Znth_injective__solver_traversal_steps :
  forall (A : Type) (values : list A) (d : A) i j,
    NoDup values ->
    0 <= i < Zlength values ->
    0 <= j < Zlength values ->
    Znth i values d = Znth j values d ->
    i = j.
Proof.
  intros A values d i j Hnodup Hi Hj Heq.
  unfold Znth in Heq.
  apply Z2Nat.inj; try lia.
  apply (proj1 (NoDup_nth values d)); try assumption.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
Qed.
Lemma traversal_append_state__solver_traversal_steps :
  forall n edges processed order_data parent_cells vertex fresh,
    TreeAttachmentCut edges ->
    TraversalState n edges processed order_data parent_cells ->
    processed < Zlength order_data ->
    vertex = Znth processed order_data 0 ->
    0 <= fresh < n ->
    ~ In fresh order_data ->
    Zlength order_data < n ->
    (In (fresh + 1, vertex + 1) edges \/
     In (vertex + 1, fresh + 1) edges) ->
    TraversalState n edges processed
      (order_data ++ (fresh :: nil))
      (replace_Znth fresh (Some vertex) parent_cells).
Proof.
  intros n edges processed order_data parent_cells vertex fresh Hcut Htrav
    Hprocessed Hvertex Hfresh_bounds Hfresh_notin Hfresh_length Hedge_attach.
  pose proof Htrav as Htrav_copy.
  pose proof (connected_prefix_of_traversal__solver_traversal_steps
    n edges processed order_data parent_cells Htrav_copy) as Hconnected.
  unfold TraversalState in Htrav.
  destruct Htrav as
    [Hcells [Hproc [Hlen [Hnodup [Hroot
     [Hvertices [Hprocessed_neighbors Hpending]]]]]]].
  assert (Hvertex_in : In vertex order_data).
  { rewrite Hvertex. apply Znth_In__solver_traversal_finish. lia. }
  unfold TraversalState.
  split.
  - rewrite Zlength_replace_Znth__solver_traversal_steps. exact Hcells.
  - split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      * split.
        -- apply NoDup_app. repeat split.
           ++ exact Hnodup.
           ++ constructor.
              ** simpl. tauto.
              ** constructor.
           ++ intros x Hx [Hx' | Hnil].
              ** subst x. contradiction.
              ** contradiction.
        -- split.
           ++ rewrite Znth_app_left__solver_traversal_steps by lia.
              exact Hroot.
           ++ split.
              ** intros q Hq. simpl.
                 rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
                 destruct (Z_lt_ge_dec q (Zlength order_data)) as [Hqold | Hqnew].
                 --- pose proof (Hvertices q ltac:(lia)) as Hold.
                     simpl in Hold.
                     destruct Hold as [Hy [pv [Hcell Hshape]]].
                     rewrite Znth_app_left__solver_traversal_steps by lia.
                     split; [exact Hy |]. exists pv. split.
                     +++ rewrite Znth_replace_Znth_Diff; try assumption; try lia.
                         intro Heq. apply Hfresh_notin.
                         rewrite Heq. apply Znth_In__solver_traversal_finish. lia.
                     +++ destruct Hshape as [Hroot_shape | Hparent_shape].
                         { left. exact Hroot_shape. }
                         right.
                         destruct Hparent_shape as
                           [parent_pos [Hparent_pos [Hpveq Hedge]]].
                         exists parent_pos. split; [exact Hparent_pos |].
                         split; [| exact Hedge].
                         rewrite Znth_app_left__solver_traversal_steps by lia.
                         exact Hpveq.
                 --- assert (Hqeq : q = Zlength order_data) by lia. subst q.
                     rewrite Znth_app_last__solver_traversal_steps.
                     split; [exact Hfresh_bounds |].
                     exists vertex. split.
                     +++ apply Znth_replace_Znth_Same. lia.
                     +++ right. exists processed. split; [lia |].
                         split; [| exact Hedge_attach].
                         rewrite Znth_app_left__solver_traversal_steps by lia.
                         exact Hvertex.
              ** split.
                 --- intros q neighbor Hq Hedge.
                     rewrite Znth_app_left__solver_traversal_steps in Hedge by lia.
                     apply in_or_app. left.
                     apply (Hprocessed_neighbors q neighbor Hq Hedge).
                 --- intros q neighbor pv Hq Hcell Hedge Hneq.
                     rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
                     destruct (Z_lt_ge_dec q (Zlength order_data)) as [Hqold | Hqnew].
                     +++ rewrite Znth_app_left__solver_traversal_steps in Hcell by lia.
                         rewrite Znth_app_left__solver_traversal_steps in Hedge by lia.
                         assert (Hy_bounds := proj1 (Hvertices q ltac:(lia))).
                         assert (Hy_neq_fresh : Znth q order_data 0 <> fresh).
                         { intro Heq. apply Hfresh_notin.
                           rewrite <- Heq.
                           apply Znth_In__solver_traversal_finish. lia. }
                         rewrite Znth_replace_Znth_Diff in Hcell;
                           try exact Hy_neq_fresh; try lia.
                         assert (Hy_neq_vertex : Znth q order_data 0 <> vertex).
                         { intro Heq. rewrite Hvertex in Heq.
                           pose proof (nodup_Znth_injective__solver_traversal_steps
                             Z order_data 0 q processed Hnodup ltac:(lia)
                             ltac:(lia) Heq) as Hidx. lia. }
                         assert (Hnot_old : ~ In neighbor order_data).
                         { apply (Hpending q neighbor pv).
                           - lia.
                           - exact Hcell.
                           - exact Hedge.
                           - exact Hneq. }
                         intros Hin_app.
                         apply in_app_or in Hin_app.
                         destruct Hin_app as [Hin_old | [Hneighbor_fresh | Hnil]].
                         { contradiction. }
                         { subst neighbor.
                           assert (Hedge_cut :
                             In (fresh + 1, Znth q order_data 0 + 1) edges \/
                             In (Znth q order_data 0 + 1, fresh + 1) edges).
                           { destruct Hedge as [Hedge | Hedge];
                               [right | left]; exact Hedge. }
                           pose proof (Hcut order_data fresh vertex
                             (Znth q order_data 0) Hnodup Hconnected
                             Hfresh_notin Hvertex_in Hedge_attach Hedge_cut
                             Hy_neq_vertex) as Hcut_q.
                           apply Hcut_q. apply in_or_app. left.
                           apply Znth_In__solver_traversal_finish. lia. }
                         { contradiction. }
                     +++ assert (Hqeq : q = Zlength order_data) by lia. subst q.
                         rewrite Znth_app_last__solver_traversal_steps in Hcell.
                         rewrite Znth_app_last__solver_traversal_steps in Hedge.
                         rewrite Znth_replace_Znth_Same in Hcell by lia.
                         injection Hcell as Hpv. subst pv.
                         apply (Hcut order_data fresh vertex neighbor Hnodup
                           Hconnected Hfresh_notin Hvertex_in Hedge_attach
                           Hedge Hneq).
Qed.
Lemma traversal_adj_parent_next_length__solver_traversal_steps :
  forall n k edges processed order_data parent_cells
    head_data to_data next_data vertex parent_vertex cursor,
    Pre n k edges ->
    AdjacencyModel n edges head_data to_data next_data ->
    processed < Zlength order_data ->
    vertex = Znth processed order_data 0 ->
    cursor <> -1 ->
    Znth cursor to_data 0 = parent_vertex ->
    TraversalAdjState n edges processed order_data parent_cells
      head_data to_data next_data vertex parent_vertex cursor ->
    Znth cursor next_data (-1) <> -1 ->
    Znth (Znth cursor next_data (-1)) to_data 0 <> parent_vertex ->
    Zlength order_data < n.
Proof.
  intros n k edges processed order_data parent_cells head_data to_data
    next_data vertex parent_vertex cursor Hpre Hmodel Hprocessed Hvertex
    Hcursor Hto Hadj Hnext Hnext_parent.
  pose proof (traversal_adj_advance_parent__solver_traversal_steps
    n k edges processed order_data parent_cells head_data to_data next_data
    vertex parent_vertex cursor Hpre Hmodel Hprocessed Hvertex Hcursor Hto
    Hadj) as Hadvanced.
  unfold TraversalAdjState in Hadvanced.
  destruct Hadvanced as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hcurrent_fresh _]]]]]]]]].
  exact (proj2 (Hcurrent_fresh Hnext Hnext_parent)).
Qed.
Lemma adjacency_reach_le__solver_traversal_steps :
  forall n next_data from slot,
    Zlength next_data = 2 * n - 2 ->
    (forall q, 0 <= q < 2 * n - 2 ->
      Znth q next_data (-1) = -1 \/
      0 <= Znth q next_data (-1) < q) ->
    0 <= slot ->
    clos_refl_trans (AdjacencyNext next_data) from slot ->
    slot <= from.
Proof.
  intros n next_data from slot Hlength Hnext Hslot Hreach.
  unfold clos_refl_trans in Hreach. sets_unfold in Hreach.
  destruct Hreach as [steps Hsteps].
  revert from Hsteps.
  induction steps as [|steps IH]; intros from Hsteps.
  - simpl in Hsteps. sets_unfold in Hsteps. subst slot. lia.
  - simpl in Hsteps. sets_unfold in Hsteps.
    destruct Hsteps as [middle [Hedge Htail]].
    unfold AdjacencyNext in Hedge.
    destruct Hedge as [Hfrom Hmiddle]. subst middle.
    specialize (IH (Znth from next_data (-1)) Htail).
    specialize (Hnext from ltac:(rewrite <- Hlength; exact Hfrom)).
    destruct Hnext; lia.
Qed.
Lemma traversal_adj_append_advance__solver_traversal_steps :
  forall n k edges processed order_data parent_cells
    head_data to_data next_data vertex parent_vertex cursor,
    Pre n k edges -> TreeAttachmentCut edges ->
    AdjacencyModel n edges head_data to_data next_data ->
    processed < Zlength order_data ->
    vertex = Znth processed order_data 0 ->
    cursor <> -1 ->
    Znth cursor to_data 0 <> parent_vertex ->
    TraversalAdjState n edges processed order_data parent_cells
      head_data to_data next_data vertex parent_vertex cursor ->
    TraversalAdjState n edges processed
      (order_data ++ (Znth cursor to_data 0 :: nil))
      (replace_Znth (Znth cursor to_data 0) (Some vertex) parent_cells)
      head_data to_data next_data vertex parent_vertex
      (Znth cursor next_data (-1)).
Proof.
  intros n k edges processed order_data parent_cells head_data to_data
    next_data vertex parent_vertex cursor Hpre Hcut Hmodel Hprocessed Hvertex
    Hcursor_nonterm Hcursor_notparent Hadj.
  pose proof Hadj as Hadj_copy.
  unfold TraversalAdjState in Hadj.
  destruct Hadj as
    [Htrav [Hcursor_bounds [Hvertex_bounds [Hparent [Hslot
     [Hscanned [Hfresh [Hcurrent_bounds [Hcurrent_fresh Hdone]]]]]]]]].
  assert (Hcursor_slot : AdjacencySlot head_data next_data vertex cursor).
  { destruct Hslot; [contradiction | assumption]. }
  pose proof (Hcurrent_fresh Hcursor_nonterm Hcursor_notparent)
    as [Hnew_notin Hlength_lt].
  pose proof (Hcurrent_bounds Hcursor_nonterm) as Hnew_bounds.
  pose proof (adjacency_slot_edge__solver_traversal_steps
    n edges head_data to_data next_data vertex cursor Hmodel
    Hvertex_bounds Hcursor_slot) as Hedge_attach.
  assert (Hedge_attach' :
    In (Znth cursor to_data 0 + 1, vertex + 1) edges \/
    In (vertex + 1, Znth cursor to_data 0 + 1) edges).
  { destruct Hedge_attach; [right | left]; assumption. }
  pose proof (traversal_append_state__solver_traversal_steps
    n edges processed order_data parent_cells vertex
    (Znth cursor to_data 0) Hcut Htrav Hprocessed Hvertex Hnew_bounds
    Hnew_notin Hlength_lt Hedge_attach') as Hnewtrav.
  assert (Hcursor_range : 0 <= cursor < Zlength next_data).
  { unfold AdjacencySlot in Hcursor_slot. tauto. }
  assert (Hnext_bounds :
    -1 <= Znth cursor next_data (-1) < 2 * n - 2).
  { unfold AdjacencyModel in Hmodel.
    destruct Hmodel as [_ [_ [_ [_ [_ [Hslots _]]]]]].
    specialize (Hslots cursor ltac:(lia)). lia. }
  assert (Hnext_range : Znth cursor next_data (-1) <> -1 ->
    0 <= Znth cursor next_data (-1) < Zlength next_data).
  { intros Hneq. unfold AdjacencyModel in Hmodel.
    destruct Hmodel as [_ [_ [Hnext_length _]]].
    rewrite Hnext_length. lia. }
  assert (Hprocessed_nonneg : 0 <= processed).
  { unfold TraversalState in Htrav. tauto. }
  assert (Hparent_length : Zlength parent_cells = n).
  { unfold TraversalState in Htrav. tauto. }
  assert (Hvertex_notnew : vertex <> Znth cursor to_data 0).
  { intro Heq. apply Hnew_notin. rewrite <- Heq, Hvertex.
    apply Znth_In__solver_traversal_finish. lia. }
  unfold TraversalAdjState.
  split; [exact Hnewtrav |].
  split; [exact Hnext_bounds |].
  split; [exact Hvertex_bounds |].
  split.
  - rewrite Znth_replace_Znth_Diff; try exact Hvertex_notnew;
      try rewrite Hparent_length; try lia.
    exact Hparent.
  - split.
    + destruct (Z.eq_dec (Znth cursor next_data (-1)) (-1)) as [Heq | Hneq].
      * left. exact Heq.
      * right. apply adjacency_slot_next__solver_traversal_steps;
          [exact Hcursor_slot | apply Hnext_range; exact Hneq].
    + split.
      * intros slot Hslot' Hbefore.
        destruct (Z.eq_dec slot cursor) as [-> | Hneqslot].
        -- apply in_or_app. right. simpl. tauto.
        -- apply in_or_app. left. apply Hscanned; [exact Hslot' |].
           right. intro Hreach.
           destruct Hbefore as [Hnext_term | Hnotreach].
           ++ pose proof (adjacency_next_tail__solver_traversal_steps
                next_data cursor slot Hreach ltac:(congruence)) as Htail.
              rewrite Hnext_term in Htail.
              pose proof Hslot' as Hslot_copy.
              unfold AdjacencySlot in Hslot_copy.
              destruct Hslot_copy as [_ [Hslot_range _]].
              pose proof (adjacency_reach_le__solver_traversal_steps
                n next_data (-1) slot ltac:(
                  unfold AdjacencyModel in Hmodel; tauto) ltac:(
                  unfold AdjacencyModel in Hmodel;
                  destruct Hmodel as [_ [_ [_ [_ [_ [Hslots _]]]]]];
                  intros q Hq; exact (proj2 (Hslots q Hq))) ltac:(lia) Htail).
              lia.
           ++ apply Hnotreach.
              apply (adjacency_next_tail__solver_traversal_steps
                next_data cursor slot Hreach ltac:(congruence)).
      * split.
        -- intros slot Hslot' Hreach Hnotparent.
           assert (Hold_notin : ~ In (Znth slot to_data 0) order_data).
           { apply (Hfresh slot Hslot').
             - apply adjacency_next_cons__solver_traversal_steps;
                 [exact Hcursor_range | exact Hreach].
             - exact Hnotparent. }
           assert (Hslot_notcursor : slot <> cursor).
           { intro Heq. subst slot.
             pose proof (adjacency_reach_le__solver_traversal_steps
               n next_data (Znth cursor next_data (-1)) cursor ltac:(
                 unfold AdjacencyModel in Hmodel; tauto) ltac:(
                 unfold AdjacencyModel in Hmodel;
                 destruct Hmodel as [_ [_ [_ [_ [_ [Hslots _]]]]]];
                 intros q Hq; exact (proj2 (Hslots q Hq))) ltac:(lia) Hreach)
               as Hle.
             unfold AdjacencyModel in Hmodel.
             destruct Hmodel as [_ [_ [_ [_ [_ [Hslots _]]]]]].
             specialize (Hslots cursor ltac:(lia)). lia. }
           assert (Hneighbor_notnew :
             Znth slot to_data 0 <> Znth cursor to_data 0).
           { intro Heq.
             unfold AdjacencyModel in Hmodel.
             destruct Hmodel as [_ [_ [_ [_ [_ [_ [_ Hunique]]]]]]].
             pose proof (Hunique vertex slot cursor Hslot' Hcursor_slot Heq).
             contradiction. }
           intro Hin. apply in_app_or in Hin.
           destruct Hin as [Hin | Hin].
           { contradiction. }
           simpl in Hin. destruct Hin as [Hin | Hin].
           { apply Hneighbor_notnew. symmetry. exact Hin. }
           { contradiction. }
        -- split.
           ++ intros Hnext_nonterm.
              unfold AdjacencyModel in Hmodel.
              destruct Hmodel as [_ [_ [_ [_ [_ [Hslots _]]]]]].
              specialize (Hslots (Znth cursor next_data (-1)) ltac:(lia)).
              exact (proj1 Hslots).
           ++ split.
              ** intros Hnext_nonterm Hnext_notparent.
                 assert (Hnext_slot : AdjacencySlot head_data next_data vertex
                   (Znth cursor next_data (-1))).
                 { apply adjacency_slot_next__solver_traversal_steps;
                     [exact Hcursor_slot | apply Hnext_range;
                       exact Hnext_nonterm]. }
                 assert (Hnext_refl : clos_refl_trans (AdjacencyNext next_data)
                   (Znth cursor next_data (-1))
                   (Znth cursor next_data (-1))).
                 { unfold clos_refl_trans. sets_unfold.
                   exists 0%nat. simpl. sets_unfold. reflexivity. }
                 assert (Hnext_notin : ~ In
                   (Znth (Znth cursor next_data (-1)) to_data 0)
                   (order_data ++ Znth cursor to_data 0 :: nil)).
                 { assert (Hold_notin : ~ In
                       (Znth (Znth cursor next_data (-1)) to_data 0)
                       order_data).
                   { apply (Hfresh (Znth cursor next_data (-1)) Hnext_slot).
                     - apply adjacency_next_cons__solver_traversal_steps;
                         [exact Hcursor_range | exact Hnext_refl].
                     - exact Hnext_notparent. }
                   assert (Hnext_index_neq :
                     Znth cursor next_data (-1) <> cursor).
                   { unfold AdjacencyModel in Hmodel.
                     destruct Hmodel as [_ [_ [_ [_ [_ [Hslots _]]]]]].
                     specialize (Hslots cursor ltac:(lia)). lia. }
                   assert (Hneighbor_neq :
                     Znth (Znth cursor next_data (-1)) to_data 0 <>
                     Znth cursor to_data 0).
                   { intro Heq. unfold AdjacencyModel in Hmodel.
                     destruct Hmodel as [_ [_ [_ [_ [_ [_ [_ Hunique]]]]]]].
                     pose proof (Hunique vertex (Znth cursor next_data (-1))
                       cursor Hnext_slot Hcursor_slot Heq). contradiction. }
                   intro Hin. apply in_app_or in Hin.
                   destruct Hin as [Hin | Hin]; [contradiction |].
                   simpl in Hin. destruct Hin as [Hin | Hin].
                   - apply Hneighbor_neq. symmetry. exact Hin.
                   - contradiction. }
                 split; [exact Hnext_notin |].
                 eapply traversal_missing_length_lt__solver_traversal_steps.
                 --- exact Hnewtrav.
                 --- unfold AdjacencyModel in Hmodel.
                     destruct Hmodel as [_ [_ [_ [_ [_ [Hslots _]]]]]].
                     specialize (Hslots (Znth cursor next_data (-1))
                       ltac:(lia)). exact (proj1 Hslots).
                 --- exact Hnext_notin.
              ** intros Hnext_term neighbor Hedge.
                 pose proof (pre_edge_bounds__solver_traversal_steps
                   n k edges vertex neighbor Hpre Hedge) as [_ Hneighbor_bounds].
                 pose proof Hmodel as Hmodel_copy.
                 unfold AdjacencyModel in Hmodel.
                 destruct Hmodel as [_ [_ [_ [_ [_ [_ [Hedges _]]]]]]].
                 destruct (proj1 (Hedges vertex neighbor Hvertex_bounds
                   Hneighbor_bounds) Hedge) as [slot [Hslot' Hto]].
                 rewrite <- Hto.
                 destruct (Z.eq_dec slot cursor) as [-> | Hneqslot].
                 --- apply in_or_app. right. simpl. tauto.
                 --- apply in_or_app. left. apply Hscanned; [exact Hslot' |].
                     right. intro Hreach.
                     pose proof (adjacency_next_tail__solver_traversal_steps
                       next_data cursor slot Hreach ltac:(congruence)) as Htail.
                     rewrite Hnext_term in Htail.
                     pose proof Hslot' as Hslot_copy.
                     unfold AdjacencySlot in Hslot_copy.
                     destruct Hslot_copy as [_ [Hslot_range _]].
                     pose proof (adjacency_reach_le__solver_traversal_steps
                       n next_data (-1) slot ltac:(
                         unfold AdjacencyModel in Hmodel_copy; tauto) ltac:(
                         unfold AdjacencyModel in Hmodel_copy;
                         destruct Hmodel_copy as [_ [_ [_ [_ [_ [Hslots _]]]]]];
                         intros q Hq; exact (proj2 (Hslots q Hq)))
                       ltac:(lia) Htail). lia.
Qed.
Lemma traversal_adj_append_next_length__solver_traversal_steps :
  forall n k edges processed order_data parent_cells
    head_data to_data next_data vertex parent_vertex cursor,
    Pre n k edges -> TreeAttachmentCut edges ->
    AdjacencyModel n edges head_data to_data next_data ->
    processed < Zlength order_data ->
    vertex = Znth processed order_data 0 ->
    cursor <> -1 ->
    Znth cursor to_data 0 <> parent_vertex ->
    TraversalAdjState n edges processed order_data parent_cells
      head_data to_data next_data vertex parent_vertex cursor ->
    Znth cursor next_data (-1) <> -1 ->
    Znth (Znth cursor next_data (-1)) to_data 0 <> parent_vertex ->
    Zlength (order_data ++ (Znth cursor to_data 0 :: nil)) < n.
Proof.
  intros n k edges processed order_data parent_cells head_data to_data
    next_data vertex parent_vertex cursor Hpre Hcut Hmodel Hprocessed Hvertex
    Hcursor Hnotparent Hadj Hnext Hnext_parent.
  pose proof (traversal_adj_append_advance__solver_traversal_steps
    n k edges processed order_data parent_cells head_data to_data next_data
    vertex parent_vertex cursor Hpre Hcut Hmodel Hprocessed Hvertex Hcursor
    Hnotparent Hadj) as Hadvanced.
  unfold TraversalAdjState in Hadvanced.
  destruct Hadvanced as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hcurrent_fresh _]]]]]]]]].
  exact (proj2 (Hcurrent_fresh Hnext Hnext_parent)).
Qed.
Lemma reachable_closed__solver_traversal_finish :
  forall edges (seen : list Z) x y,
    In (x - 1) seen ->
    (forall a b,
      In (a - 1) seen ->
      EdgePresent edges (fun _ => False) a b ->
      In (b - 1) seen) ->
    ConnectedWithout edges (fun _ => False) x y ->
    In (y - 1) seen.
Proof.
  intros edges seen x y Hx Hclosed Hconn.
  unfold ConnectedWithout, clos_refl_trans in Hconn.
  sets_unfold in Hconn.
  destruct Hconn as [steps Hsteps].
  revert x Hx Hsteps.
  induction steps as [|steps IH]; intros x Hx Hsteps.
  - simpl in Hsteps. sets_unfold in Hsteps. subst y. exact Hx.
  - simpl in Hsteps. sets_unfold in Hsteps.
    destruct Hsteps as [z [Hedge Htail]].
    apply (IH z).
    + apply (Hclosed x z Hx Hedge).
    + exact Htail.
Qed.
Lemma vertex_seq_iff__solver_traversal_finish :
  forall n x,
    0 <= n ->
    (In x (map Z.of_nat (seq 0 (Z.to_nat n))) <-> 0 <= x < n).
Proof.
  intros n x Hn. split.
  - intros Hin. apply in_map_iff in Hin.
    destruct Hin as [m [Hx Hm]].
    apply in_seq in Hm. subst x. lia.
  - intros Hx.
    apply in_map_iff.
    exists (Z.to_nat x). split.
    + lia.
    + apply in_seq. lia.
Qed.
Lemma vertex_seq_nodup__solver_traversal_finish :
  forall n, NoDup (map Z.of_nat (seq 0 n)).
Proof.
  intros n.
  apply FinFun.Injective_map_NoDup.
  - intros x y Hxy. lia.
  - apply seq_NoDup.
Qed.
Lemma options_all_some__solver_traversal_finish :
  forall (cells : list (option Z)),
    (forall i, 0 <= i < Zlength cells ->
      exists v, Znth i cells None = Some v) ->
    exists values, cells = map (@Some Z) values.
Proof.
  induction cells as [|cell cells IH]; intros Hall.
  - exists nil. reflexivity.
  - destruct cell as [v|].
    + assert (Htail : forall i : Z,
          0 <= i < Zlength cells ->
          exists v0 : Z, Znth i cells None = Some v0).
      { intros i Hi.
        specialize (Hall (i + 1)).
        rewrite Zlength_cons in Hall.
        specialize (Hall ltac:(lia)).
        rewrite Znth_cons in Hall by lia.
        replace (i + 1 - 1) with i in Hall by lia.
        exact Hall. }
      destruct (IH Htail) as [values Hvalues].
      exists (v :: values). simpl. f_equal. exact Hvalues.
    + specialize (Hall 0).
      pose proof (Zlength_nonneg cells).
      rewrite Zlength_cons in Hall.
      specialize (Hall ltac:(lia)).
      rewrite Znth0_cons in Hall.
      destruct Hall as [v Hv]. discriminate.
Qed.
Lemma Znth_map_some__solver_traversal_finish :
  forall values i d,
    0 <= i < Zlength values ->
    Znth i (map (@Some Z) values) None = Some (Znth i values d).
Proof.
  intros values i d Hi.
  revert i Hi.
  induction values as [|v values IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [->|Hne].
    + reflexivity.
    + assert (0 < i) by lia.
      change (Znth i (Some v :: map (@Some Z) values) None =
        Some (Znth i (v :: values) d)).
      rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.
Lemma traversal_complete_rooted_order__solver_traversal_finish :
  forall n k edges processed order_data parent_cells,
    Pre n k edges ->
    processed = Zlength order_data ->
    TraversalState n edges processed order_data parent_cells ->
    exists parent_data,
      Zlength order_data = n /\
      parent_cells = map (@Some Z) parent_data /\
      RootedOrderModel n edges parent_data order_data /\
      (forall j, 0 <= j < n ->
        (0 <= Znth j order_data 0 < n /\
         -1 <= Znth j parent_data 0) /\
        Znth j parent_data 0 < n).
Proof.
  intros n k edges processed order_data parent_cells Hpre Hprocessed Htrav.
  unfold Pre in Hpre.
  destruct Hpre as [Hkn [Hnmax [Hedges [Hedge_bounds [Hsimple
    [Hattachment [Hedge_fresh [Hconnected Hrest]]]]]]]].
  unfold TraversalState in Htrav.
  destruct Htrav as
    [Hcells [Hproc_bounds [Horder_bounds [Hnodup [Hroot
     [Hvertices [Hprocessed_neighbors Hunprocessed]]]]]]].
  assert (Hseen : forall v, 0 <= v < n -> In v order_data).
  { intros v Hv.
    replace v with (v + 1 - 1) by lia.
    apply (reachable_closed__solver_traversal_finish edges order_data 1 (v + 1)).
    - replace (1 - 1) with 0 by lia.
      rewrite <- Hroot.
      apply Znth_In__solver_traversal_finish.
      lia.
    - intros a b Ha Hedge.
      destruct (In_Znth__solver_traversal_finish Z order_data (a - 1) 0 Ha)
        as [q [Hq Hqa]].
      apply (Hprocessed_neighbors q (b - 1)).
      + rewrite Hprocessed. exact Hq.
      + rewrite Hqa.
        unfold EdgePresent in Hedge.
        destruct Hedge as [[Hab | Hba] _].
        * left. replace (a - 1 + 1) with a by lia.
          replace (b - 1 + 1) with b by lia. exact Hab.
        * right. replace (a - 1 + 1) with a by lia.
          replace (b - 1 + 1) with b by lia. exact Hba.
    - apply Hconnected. lia. }
  assert (Hperm :
      Permutation order_data (map Z.of_nat (seq 0 (Z.to_nat n)))).
  { apply NoDup_Permutation.
    - exact Hnodup.
    - apply vertex_seq_nodup__solver_traversal_finish.
    - intros x. split.
      + intros Hin.
        destruct (In_Znth__solver_traversal_finish Z order_data x 0 Hin)
          as [q [Hq Hqx]].
        specialize (Hvertices q Hq).
        rewrite Hqx in Hvertices.
        apply vertex_seq_iff__solver_traversal_finish; lia.
      + intros Hin.
        apply vertex_seq_iff__solver_traversal_finish in Hin; try lia.
        apply Hseen. exact Hin. }
  assert (Horderlen : Zlength order_data = n).
  { apply Permutation_length in Hperm.
    rewrite map_length, seq_length in Hperm.
    rewrite Zlength_correct.
    lia. }
  assert (Hallcells : forall idx, 0 <= idx < Zlength parent_cells ->
      exists pv, Znth idx parent_cells None = Some pv).
  { intros idx Hidx.
    assert (Hidxn : 0 <= idx < n) by lia.
    specialize (Hseen idx Hidxn).
    destruct (In_Znth__solver_traversal_finish Z order_data idx 0 Hseen)
      as [q [Hq Hqidx]].
    specialize (Hvertices q Hq).
    simpl in Hvertices.
    rewrite Hqidx in Hvertices.
    destruct Hvertices as [_ [pv [Hpv _]]].
    exists pv. exact Hpv. }
  destruct (options_all_some__solver_traversal_finish parent_cells Hallcells)
    as [parent_data Hparent_cells].
  assert (Hparentlen : Zlength parent_data = n).
  { rewrite Hparent_cells in Hcells.
    rewrite !Zlength_correct, length_map in Hcells.
    rewrite Zlength_correct. exact Hcells. }
  assert (Hroot_parent : Znth 0 parent_data (-1) = -1).
  { specialize (Hvertices 0 ltac:(lia)).
    simpl in Hvertices.
    destruct Hvertices as [_ [pv [Hpv [[_ Hpvroot] | Hbad]]]].
    - rewrite Hparent_cells in Hpv.
      rewrite Hroot in Hpv.
      rewrite (Znth_map_some__solver_traversal_finish parent_data 0 (-1))
        in Hpv by lia.
      injection Hpv as Heq. rewrite Heq. exact Hpvroot.
    - destruct Hbad as [parent_pos [Hparent_pos _]]. lia. }
  assert (Hparent_edges : forall q, 1 <= q < n ->
      exists parent_pos,
        0 <= parent_pos < q /\
        Znth (Znth q order_data 0) parent_data (-1) =
          Znth parent_pos order_data 0 /\
        (In (Znth q order_data 0 + 1,
             Znth parent_pos order_data 0 + 1) edges \/
         In (Znth parent_pos order_data 0 + 1,
             Znth q order_data 0 + 1) edges)).
  { intros q Hq.
    specialize (Hvertices q ltac:(lia)).
    simpl in Hvertices.
    destruct Hvertices as [Hvertex [pv [Hpv [Hrootcase | Hparentcase]]]].
    - lia.
    - destruct Hparentcase as [parent_pos [Hppos [Hpveq Hedge]]].
      exists parent_pos. split; [exact Hppos|]. split;
        [|rewrite <- Hpveq; exact Hedge].
      rewrite Hparent_cells in Hpv.
      rewrite (Znth_map_some__solver_traversal_finish parent_data
        (Znth q order_data 0) (-1)) in Hpv by lia.
      injection Hpv as Heq. rewrite Heq. exact Hpveq. }
  assert (Hrooted : RootedOrderModel n edges parent_data order_data).
  { unfold RootedOrderModel. intuition lia. }
  exists parent_data.
  split; [exact Horderlen|].
  split; [exact Hparent_cells|].
  split; [exact Hrooted|].
  intros j Hj.
  pose proof Hvertices as Hvertices_master.
  pose proof Hvertices as Hvertices_all.
  specialize (Hvertices j ltac:(lia)).
  simpl in Hvertices.
  destruct Hvertices as [Horder_vertex _].
  specialize (Hseen j Hj).
  destruct (In_Znth__solver_traversal_finish Z order_data j 0 Hseen)
    as [q [Hq Hqj]].
  specialize (Hvertices_all q Hq).
  simpl in Hvertices_all.
  destruct Hvertices_all as [_ [pv [Hpv Hpvshape]]].
  rewrite Hparent_cells in Hpv.
  rewrite Hqj in Hpv.
  rewrite (Znth_map_some__solver_traversal_finish parent_data j 0)
    in Hpv by lia.
  injection Hpv as Heq.
  assert (-1 <= pv < n).
  { destruct Hpvshape as [[_ Hrootv] | Hpar].
    - subst pv. lia.
    - destruct Hpar as [parent_pos [Hppos [Hpveq Hedge]]].
      specialize (Hvertices_master parent_pos ltac:(lia)).
      simpl in Hvertices_master.
      destruct Hvertices_master as [Hparent_bounds _].
      rewrite Hpveq. lia. }
  rewrite Heq. repeat split; lia.
Qed.
Lemma search_state_initial__solver_traversal_finish :
  forall n k edges,
    Pre n k edges ->
    SearchState n k edges 1 (n ÷ (k + 1)) 1.
Proof.
  intros n k edges Hpre.
  unfold Pre in Hpre.
  destruct Hpre as [Hkn [Hnmax [Hedges [Hedge_bounds [Hsimple
    [Hattachment [Hedge_fresh [Hconnected
      [Hoptimum_exists Hscan]]]]]]]]].
  destruct Hoptimum_exists as [optimum [Hspec Hoptimum]].
  unfold SearchState.
  rewrite Z.quot_div_nonneg by lia.
  assert (Hhi_nonneg : 0 <= n / (k + 1)).
  { lia. }
  assert (Hhi_le_n : n / (k + 1) <= n).
  { apply Z.div_le_upper_bound; nia. }
  split; [lia|].
  split; [lia|].
  split; [lia|].
  exists optimum.
  split; [exact Hspec|].
  split; [lia|].
  split; [lia|].
  left. lia.
Qed.
Lemma spec_unique__solver_search_transitions :
  forall n k edges first second,
    Spec n k edges first ->
    Spec n k edges second ->
    first = second.
Proof.
  intros n k edges first second Hfirst Hsecond.
  unfold Spec, max_value_of_subset, max_object_of_subset in *.
  destruct Hfirst as [first_cut [[Hfirst_legal Hfirst_max] Hfirst_value]].
  destruct Hsecond as
    [second_cut [[Hsecond_legal Hsecond_max] Hsecond_value]].
  specialize (Hfirst_max second_cut Hsecond_legal).
  specialize (Hsecond_max first_cut Hfirst_legal).
  subst first second.
  simpl in *.
  lia.
Qed.
Lemma midpoint_bounds__solver_search_transitions :
  forall lo hi,
    0 <= lo ->
    lo <= hi ->
    lo <= Z.quot (lo + hi) 2 <= hi.
Proof.
  intros lo hi Hlo Hle.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
  lia.
Qed.
Lemma search_state_closed_spec__solver_finalization :
  forall n k edges lo hi best,
    SearchState n k edges lo hi best ->
    hi < lo ->
    Spec n k edges best.
Proof.
  intros n k edges lo hi best Hstate Hclosed.
  unfold SearchState in Hstate.
  destruct Hstate as
    [_ [_ [_ [optimum [Hspec [_ [_ Hinterval]]]]]]].
  destruct Hinterval as [[Hlo Hhi] | Hbest].
  - lia.
  - destruct Hbest as [Hbest _].
    rewrite Hbest.
    exact Hspec.
Qed.
