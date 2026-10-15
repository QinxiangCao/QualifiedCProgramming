Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Notation ztriple_1 := (fun p : Z * Z * Z => fst (fst p)).
Notation ztriple_2 := (fun p : Z * Z * Z => snd (fst p)).
Notation ztriple_3 := (fun p : Z * Z * Z => snd p).

Definition SelectedRoadStep (roads : list (Z * Z * Z)) (chosen : Z -> Prop)
    (x y : Z) : Prop :=
  exists i, chosen i /\ 0 <= i < Zlength roads /\
    let '(u,v,_) := Znth i roads (0,0,0) in
    (u = x /\ v = y) \/ (u = y /\ v = x).

Definition RoadTree (n : Z) (roads : list (Z * Z * Z))
    (chosen : Z -> Prop) : Prop :=
  (forall i, chosen i -> 0 <= i < Zlength roads) /\
  #(fun i : Z => 0 <= i < Zlength roads /\ chosen i) = n - 1 /\
  forall v, 1 <= v <= n ->
    clos_refl_trans (SelectedRoadStep roads chosen) 1 v.

Definition ReformCost (k : Z) (roads : list (Z * Z * Z))
    (chosen : Z -> Prop) (new_weight : Z -> Z) (cost : Z) : Prop :=
  (exists i, chosen i /\ new_weight i = k) /\
  (forall i, chosen i -> new_weight i <= k) /\
  cost = sum (fun i : Z => 0 <= i < Zlength roads /\ chosen i)
    (fun i => Z.abs (new_weight i -
      let '(_,_,weight) := Znth i roads (0,0,0) in weight)).

Definition Pre (n k : Z) (roads : list (Z * Z * Z)) : Prop :=
  2 <= n <= 200000 /\ 1 <= k <= 1000000000 /\ n - 1 <= Zlength roads /\
  Forall (fun e => let '(u,v,w) := e in
    1 <= u <= n /\ 1 <= v <= n /\ u <> v /\ 1 <= w <= 1000000000) roads /\
  exists chosen, RoadTree n roads chosen.

Definition Spec (n k : Z) (roads : list (Z * Z * Z)) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : ((Z -> Prop) * (Z -> Z)) * Z =>
      RoadTree n roads (fst (fst candidate)) /\
      ReformCost k roads (fst (fst candidate))
        (snd (fst candidate)) (snd candidate))
    snd out.

Require Import Coq.Sorting.Permutation.
Require AUXLib.ListLib.
Import ListNotations.

(** The declarations below expose the mathematical behavior of the local C
    helpers.  They deliberately describe an encoded edge sequence, a sorted
    permutation, and a disjoint-set partition rather than replaying either
    helper's control flow. *)

Definition RoadU (e : Z * Z * Z) : Z :=
  let '(u, _, _) := e in u.

Definition RoadV (e : Z * Z * Z) : Z :=
  let '(_, v, _) := e in v.

Definition RoadW (e : Z * Z * Z) : Z :=
  let '(_, _, w) := e in w.

Definition RoadEncoding (roads : list (Z * Z * Z)) (raw : list Z) : Prop :=
  Zlength raw = 4 * Zlength roads /\
  forall i, 0 <= i < Zlength roads ->
    Znth (4 * i) raw 0 = RoadU (Znth i roads (0, 0, 0)) - 1 /\
    Znth (4 * i + 1) raw 0 = RoadV (Znth i roads (0, 0, 0)) - 1.

Definition EdgeBlock (road : Z * Z * Z) (raw : list Z) : Prop :=
  RoadEncoding [road] raw.

Definition RoadWeightSorted (roads : list (Z * Z * Z)) : Prop :=
  ListLib.increasing (map RoadW roads).

Definition RoadSortResult
    (original sorted : list (Z * Z * Z))
    (raw order : list Z) : Prop :=
  Zlength sorted = Zlength original /\
  Zlength order = Zlength original /\
  Permutation order (map Z.of_nat (seq 0 (Z.to_nat (Zlength original)))) /\
  (forall i, 0 <= i < Zlength sorted ->
    Znth i sorted (0, 0, 0) =
      Znth (Znth i order 0) original (0, 0, 0)) /\
  RoadWeightSorted sorted /\
  RoadEncoding sorted raw.

Definition RoadCompareResult
    (left right : Z * Z * Z) (out : Z) : Prop :=
  (RoadW left < RoadW right /\ out = -1) \/
  (RoadW left = RoadW right /\ out = 0) \/
  (RoadW right < RoadW left /\ out = 1).

Definition ChosenRoad (chosen : list Z) (i : Z) : Prop := In i chosen.

Definition RoadConnected
    (roads : list (Z * Z * Z)) (chosen : list Z) (x y : Z) : Prop :=
  clos_refl_trans (SelectedRoadStep roads (ChosenRoad chosen)) x y.

Definition ParentStep (parents : list Z) (x y : Z) : Prop :=
  0 <= x < Zlength parents /\ x <> y /\ y = Znth x parents 0.

Definition ParentRoot (parents : list Z) (x root : Z) : Prop :=
  0 <= x < Zlength parents /\
  0 <= root < Zlength parents /\
  clos_refl_trans (ParentStep parents) x root /\
  Znth root parents 0 = root.

Definition DSUState
    (n : Z) (roads : list (Z * Z * Z))
    (chosen parents : list Z) : Prop :=
  Zlength parents = n /\
  NoDup chosen /\
  (forall i, In i chosen -> 0 <= i < Zlength roads) /\
  (forall x, 0 <= x < n -> exists root, ParentRoot parents x root) /\
  forall x y, 0 <= x < n -> 0 <= y < n ->
    (RoadConnected roads chosen (x + 1) (y + 1) <->
      exists root, ParentRoot parents x root /\ ParentRoot parents y root).

Definition DSUFindResult
    (n : Z) (roads : list (Z * Z * Z)) (chosen : list Z)
    (before after : list Z) (x root : Z) : Prop :=
  DSUState n roads chosen before /\
  DSUState n roads chosen after /\
  ParentRoot after x root /\
  Znth root after 0 = root.

(** Body-only semantic states, designed from the static annotation points. *)

Definition FindProgress
    (n : Z) (roads : list (Z * Z * Z)) (chosen : list Z)
    (query current : Z) (parents : list Z) : Prop :=
  DSUState n roads chosen parents /\
  RoadConnected roads chosen (query + 1) (current + 1).

Definition ClosestRoadPrefix
    (k : Z) (roads : list (Z * Z * Z))
    (processed closest : Z) : Prop :=
  (processed = 0 /\ closest = 4611686018427387904) \/
  (0 < processed /\
   min_value_of_subset Z.le
     (fun i : Z => 0 <= i < processed)
     (fun i => Z.abs (RoadW (Znth i roads (0, 0, 0)) - k))
     closest).

Definition ExtendableRoadForest
    (n : Z) (roads : list (Z * Z * Z)) (selected : list Z) : Prop :=
  NoDup selected /\
  (forall i, In i selected -> 0 <= i < Zlength roads) /\
  exists tree,
    RoadTree n roads tree /\
    forall i, In i selected -> tree i.

Definition SelectedExcess
    (k : Z) (roads : list (Z * Z * Z))
    (selected : list Z) (excess : Z) : Prop :=
  excess = sum
    (fun i : Z => 0 <= i < Zlength roads /\ In i selected)
    (fun i => Z.max 0 (RoadW (Znth i roads (0, 0, 0)) - k)).

Definition MinimumExcessForest
    (n k : Z) (roads : list (Z * Z * Z))
    (selected : list Z) (used excess : Z) : Prop :=
  ExtendableRoadForest n roads selected /\
  Zlength selected = used /\
  SelectedExcess k roads selected excess /\
  forall other other_excess,
    ExtendableRoadForest n roads other ->
    Zlength other = used ->
    SelectedExcess k roads other other_excess ->
    excess <= other_excess.

Definition EdgeEndpointsConnected
    (roads : list (Z * Z * Z)) (selected : list Z) (edge_index : Z) : Prop :=
  let edge := Znth edge_index roads (0, 0, 0) in
  RoadConnected roads selected (RoadU edge) (RoadV edge).

Definition KruskalPrefixState
    (n k : Z) (roads sorted : list (Z * Z * Z)) (order : list Z)
    (processed : Z) (selected : list Z) (used excess : Z) : Prop :=
  (exists raw, RoadSortResult roads sorted raw order) /\
  (forall edge_index, In edge_index selected ->
    exists j, 0 <= j < processed /\ Znth j order 0 = edge_index) /\
  (forall j, 0 <= j < processed ->
    In (Znth j order 0) selected \/
    EdgeEndpointsConnected roads selected (Znth j order 0)) /\
  MinimumExcessForest n k roads selected used excess.

(** Transparent projections give proving workers the exact mathematical bridge
    facts without changing the frozen predicate meanings. *)
Lemma kruskal_prefix_extendable :
  forall n k roads sorted order processed selected used excess,
    KruskalPrefixState n k roads sorted order processed selected used excess ->
    ExtendableRoadForest n roads selected.
Proof.
  intros n k roads sorted order processed selected used excess H.
  unfold KruskalPrefixState, MinimumExcessForest in H.
  tauto.
Qed.

Lemma kruskal_prefix_cardinality :
  forall n k roads sorted order processed selected used excess,
    KruskalPrefixState n k roads sorted order processed selected used excess ->
    Zlength selected = used.
Proof.
  intros n k roads sorted order processed selected used excess H.
  unfold KruskalPrefixState, MinimumExcessForest in H.
  tauto.
Qed.

Lemma kruskal_prefix_accumulator :
  forall n k roads sorted order processed selected used excess,
    KruskalPrefixState n k roads sorted order processed selected used excess ->
    SelectedExcess k roads selected excess.
Proof.
  intros n k roads sorted order processed selected used excess H.
  unfold KruskalPrefixState, MinimumExcessForest in H.
  tauto.
Qed.

(** A native representation for arrays of the anonymous C [Edge] structure.
    It deliberately uses the same opaque structure-size and field-address
    operations as symbolic execution.  Consequently no numeric layout axiom
    (such as [sizeof Edge = 16]) is needed. *)
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.

Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string_scope.

Definition store_road_edge
    (base : addr) (i : Z) (road : Z * Z * Z) : Assertion :=
  let p := base + i * sizeof_front_end_type (FET_alias "<anonymous struct>") in
  (&((p) # "anonymous struct 1" ->ₛ "u") # Int |-> (RoadU road - 1)) **
  (&((p) # "anonymous struct 1" ->ₛ "v") # Int |-> (RoadV road - 1)) **
  (&((p) # "anonymous struct 1" ->ₛ "w") # Int64 |-> RoadW road).

Definition undef_road_edge (base : addr) (i : Z) : Assertion :=
  let p := base + i * sizeof_front_end_type (FET_alias "<anonymous struct>") in
  (&((p) # "anonymous struct 1" ->ₛ "u") # Int |->_) **
  (&((p) # "anonymous struct 1" ->ₛ "v") # Int |->_) **
  (&((p) # "anonymous struct 1" ->ₛ "w") # Int64 |->_).

Module EdgeArray.

Definition full
    (base : addr) (n : Z) (roads : list (Z * Z * Z)) : Assertion :=
  store_array store_road_edge base n roads.

Definition missing_i
    (base : addr) (i lo hi : Z) (roads : list (Z * Z * Z)) : Assertion :=
  store_array_missing_i_rec store_road_edge base i lo hi roads.

Definition undef_full (base : addr) (n : Z) : Assertion :=
  store_undef_array undef_road_edge base n.

Definition undef_missing_i
    (base : addr) (i lo hi : Z) : Assertion :=
  store_undef_array_missing_i_rec undef_road_edge base i lo hi
    (Z.to_nat (hi - lo)).

End EdgeArray.

(** The allocation/sort boundary uses the same opaque front-end size that
    indexes [store_road_edge].  This avoids both an unsupported C typedef in
    annotation syntax and any numeric record-layout assumption. *)
Definition EdgeAllocationSize (size cap : Z) : Prop :=
  size = cap * sizeof_front_end_type (FET_alias "<anonymous struct>").

(** Exact no-wrap condition for the 32-bit [size_t] model used by the
    generated allocation call.  The record size remains QCP's opaque
    front-end size; no concrete ABI layout is assumed. *)
Definition EdgeAllocationFits (cap : Z) : Prop :=
  0 <= cap * sizeof_front_end_type (FET_alias "<anonymous struct>") < 2 ^ 32.

(** The C expression casts [cap] to the 32-bit unsigned [size_t] model and
    then performs unsigned multiplication.  Under the frozen no-wrap
    premise, both truncations are identities. *)
Lemma edge_allocation_fits_size :
  forall cap,
    0 <= cap < 2 ^ 32 ->
    EdgeAllocationFits cap ->
    EdgeAllocationSize
      (unsigned_last_nbits
        (unsigned_last_nbits cap 32 *
          sizeof_front_end_type (FET_alias "<anonymous struct>")) 32)
      cap.
Proof.
  intros cap Hcap Hfits.
  unfold EdgeAllocationFits in Hfits.
  unfold EdgeAllocationSize.
  rewrite (unsigned_last_nbits_eq cap 32 Hcap).
  rewrite (unsigned_last_nbits_eq
    (cap * sizeof_front_end_type (FET_alias "<anonymous struct>"))
    32 Hfits).
  reflexivity.
Qed.

(** Path halving only rewrites non-root parent cells.  This transition is
    deliberately stronger than abstract partition preservation: every
    concrete root of the input representation remains the same concrete
    root afterward. *)
Definition DSURootsPreserved (before after : list Z) : Prop :=
  forall root,
    0 <= root < Zlength before ->
    Znth root before 0 = root ->
    Znth root after 0 = root.
