Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.DFS Require Export concrete_graphs.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
From MonadLib.StateRelMonad Require Import StateRelBasic.
Require Import Algorithms.DFS.DFS.
Require Import GraphLib.reachable.reachable_basic.

Import ListNotations.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition applyf {A B : Type} (f : A -> B) (a : A) : B := f a.

Module DFSAdjacencyList.

(** Annotation-facing specialization: [E] is not determined by [G] and [V],
    so Rocq cannot infer the concrete [Graph G V E] instance from [DFS g u]. *)
Definition dfs_program
    (g : ZSimpleGraph.G) (u : Z) : program (Z -> Prop) unit :=
  @DFS ZSimpleGraph.G Z ZSimpleGraph.E ZSimpleGraph.graph_instance g u.

Definition dfs_step
    (g : ZSimpleGraph.G) (u v : Z) : Prop :=
  @step ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance g u v.

Definition dfs_loop
    (g : ZSimpleGraph.G) (u : Z) : program (Z -> Prop) unit :=
  whileP
    (fun visited_set => exists v, dfs_step g u v /\ ~ visited_set v)
    (v <- get (fun visited_set v =>
      dfs_step g u v /\ ~ visited_set v);;
     dfs_program g v).

Definition dfs_continue
    (g : ZSimpleGraph.G) (u : Z) (_ : unit)
    : program (Z -> Prop) unit :=
  dfs_loop g u.

Definition is_reachable
    (g : ZSimpleGraph.G) (source target : Z) : Prop :=
  @reachable ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance g source target.

Fixpoint addressed_sll
    (cursor : addr) (node_addrs : list addr) (values : list Z)
    : Assertion :=
  match node_addrs, values with
  | nil, nil => “ cursor = NULL ” && emp
  | node :: node_addrs', datum :: values' =>
      “ cursor = node /\ node <> NULL ” &&
      EX next : addr,
        &(node # "list" ->ₛ "data") # Int |-> datum **
        &(node # "list" ->ₛ "next") # Ptr |-> next **
        addressed_sll next node_addrs' values'
  | _, _ => “ False ”
  end.

Fixpoint addressed_sllseg
    (cursor stop : addr) (node_addrs : list addr) (values : list Z)
    : Assertion :=
  match node_addrs, values with
  | nil, nil => “ cursor = stop ” && emp
  | node :: node_addrs', datum :: values' =>
      “ cursor = node /\ node <> NULL ” &&
      EX next : addr,
        &(node # "list" ->ₛ "data") # Int |-> datum **
        &(node # "list" ->ₛ "next") # Ptr |-> next **
        addressed_sllseg next stop node_addrs' values'
  | _, _ => “ False ”
  end.

Definition row_block
    (entry : addr * (list addr * list Z)) : Assertion :=
  addressed_sll (fst entry) (fst (snd entry)) (snd (snd entry)).

Definition list_blocks
    (row_ptrs : list addr) (node_addrs : list (list addr))
    (rows : list (list Z)) : Assertion :=
  iter_sepcon
    (map row_block (combine row_ptrs (combine node_addrs rows))).

Definition list_blocks_missing
    (u : Z) (row_ptrs : list addr) (node_addrs : list (list addr))
    (rows : list (list Z)) : Assertion :=
  iter_sepcon
    (map row_block
      (PtrPtrArray2.remove_Znth u
        (combine row_ptrs (combine node_addrs rows)))).

Definition all_visited
    (vertices : list Z) (visited_set : Z -> Prop) : Prop :=
  forall v, In v vertices -> visited_set v.

(** A DFS call only adds vertices to the caller's visited set. *)
Definition visited_extension
    (before after : Z -> Prop) : Prop :=
  forall v, before v -> after v.

Definition empty_visited (visited_set : Z -> Prop) : Prop :=
  forall v, ~ visited_set v.

(** The head-pointer array and all linked lists it owns.  Both ghost lists
    are explicit here so a recursive proof can keep their order fixed while
    splitting out and later restoring one adjacency row. *)
Definition linked_lists_rep
    (adjacency : addr) (vertex_count : Z)
    (row_ptrs : list addr) (node_addrs : list (list addr))
    (rows : list (list Z))
    : Assertion :=
  “ Zlength row_ptrs = vertex_count /\
    Zlength node_addrs = vertex_count /\
    Zlength rows = vertex_count ” &&
  PtrArray.full adjacency vertex_count row_ptrs **
  list_blocks row_ptrs node_addrs rows.

(** A convenience layer that fixes the row contents but hides the physical
    array of list-head pointers. *)
Definition linked_lists
    (adjacency : addr) (vertex_count : Z) (rows : list (list Z))
    : Assertion :=
  EX row_ptrs : list addr, EX node_addrs : list (list addr),
    linked_lists_rep adjacency vertex_count row_ptrs node_addrs rows.

(** The logical contents of every row exactly enumerate the outgoing
    neighbors in the concrete simple graph. *)
Definition adjacency_lists_model
    (g : ZSimpleGraph.G) (rows : list (list Z)) : Prop :=
  ZSimpleGraph.graph_wf g /\
  Zlength rows = ZSimpleGraph.vertex_count g /\
  Forall (fun row => NoDup row) rows /\
  forall u v,
    ZSimpleGraph.vertex_valid g u ->
    (In v (Znth u rows nil) <-> ZSimpleGraph.graph_step g u v).

(** Representation exposed to the recursive C proof.  [row_ptrs] and [rows]
    are immutable witnesses and therefore remain identical in the pre- and
    postcondition of every recursive call. *)
Definition graph_rep
    (adjacency : addr) (g : ZSimpleGraph.G)
    (row_ptrs : list addr) (node_addrs : list (list addr))
    (rows : list (list Z)) : Assertion :=
  “ adjacency_lists_model g rows ” &&
  linked_lists_rep
    adjacency (ZSimpleGraph.vertex_count g) row_ptrs node_addrs rows.

(** The immutable graph representation with row [u] removed.  The caller
    separately owns the pointer-array cell and the split linked-list row. *)
Definition graph_except
    (adjacency : addr) (g : ZSimpleGraph.G)
    (row_ptrs : list addr) (node_addrs : list (list addr))
    (rows : list (list Z)) (u : Z)
    : Assertion :=
  “ adjacency_lists_model g rows /\
    Zlength row_ptrs = ZSimpleGraph.vertex_count g /\
    Zlength node_addrs = ZSimpleGraph.vertex_count g /\
    Zlength rows = ZSimpleGraph.vertex_count g /\
    ZSimpleGraph.vertex_valid g u ” &&
  PtrArray.missing_i
    adjacency u 0 (ZSimpleGraph.vertex_count g) row_ptrs **
  list_blocks_missing u row_ptrs node_addrs rows.

(** Intermediate abstraction for clients that need the fixed row order but
    do not need to name the concrete list-head pointers. *)
Definition graph_with_rows
    (adjacency : addr) (g : ZSimpleGraph.G) (rows : list (list Z))
    : Assertion :=
  EX row_ptrs : list addr, EX node_addrs : list (list addr),
    graph_rep adjacency g row_ptrs node_addrs rows.

(** Public graph predicate: the storage order is irrelevant to clients. *)
Definition graph (adjacency : addr) (g : ZSimpleGraph.G) : Assertion :=
  EX rows : list (list Z),
    graph_with_rows adjacency g rows.

Definition visited
    (visited_ptr : addr) (g : ZSimpleGraph.G) (visited_set : Z -> Prop)
    : Assertion :=
  EX values : list Z,
    “ ZSimpleGraph.visited_values g values visited_set ” &&
    IntArray.full visited_ptr (ZSimpleGraph.vertex_count g) values.

End DFSAdjacencyList.

Require Import Coq.micromega.Lia.
Lemma visited_values_after_visit__execution_representation :
  forall g values before u,
    ZSimpleGraph.visited_values g values before ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.visited_values g (replace_Znth u 1 values)
      (fun v => before v \/ v = u).
Proof.
  intros g values before u Hvalues Hu.
  unfold ZSimpleGraph.visited_values in *.
  destruct Hvalues as [Hlen [Hvalid Hvalue]].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + intros v [Hv | ->]; auto.
    + intros v Hv.
      specialize (Hvalue v Hv) as [H01 Hiff].
      destruct (Z.eq_dec v u) as [-> | Hne].
      * rewrite Znth_replace_Znth_Same by
            (unfold ZSimpleGraph.vertex_valid in *; lia).
        split; [auto |].
        split; [tauto | intros; right; reflexivity].
      * rewrite Znth_replace_Znth_Diff by
            (unfold ZSimpleGraph.vertex_valid in *; lia).
        split; [exact H01 |].
        split.
        -- intros [Hb | Heq]; [apply Hiff; exact Hb | contradiction].
        -- intros Hbit. left. apply Hiff. exact Hbit.
Qed.
Lemma iter_sepcon_split_remove_Znth__execution_representation :
  forall {B : Type} (P : B -> Assertion) i (l : list B) d,
    0 <= i < Zlength l ->
    iter_sepcon (map P l) |--
      P (Znth i l d) **
      iter_sepcon (map P (PtrPtrArray2.remove_Znth i l)).
Proof.
  intros B P i l d Hi.
  unfold PtrPtrArray2.remove_Znth.
  rewrite (firstn_skipSn d (Z.to_nat i) l) at 1 by
    (rewrite Zlength_correct in Hi; lia).
  unfold Znth.
  rewrite !map_app.
  change (map P (firstn (Z.to_nat i) l) ++
          P (nth (Z.to_nat i) l d) :: map P (skipn (S (Z.to_nat i)) l))
    with (map P (firstn (Z.to_nat i) l) ++
          [P (nth (Z.to_nat i) l d)] ++
          map P (skipn (S (Z.to_nat i)) l)).
  rewrite derivable1_sepcon_iter_sepcon2.
  sep_apply (derivable1_sepcon_iter_sepcon2
    [P (nth (Z.to_nat i) l d)]
    (map P (skipn (S (Z.to_nat i)) l))).
  rewrite derivable1_iter_sepcon_l.
  simpl.
  rewrite <- derivable1_sepcon_iter_sepcon1.
  entailer!.
  all: entailer!.
  rewrite derivable1_iter_sepcon_l.
  simpl.
  entailer!.
Qed.
Lemma Znth_combine__execution_representation :
  forall {B C : Type} i (l1 : list B) (l2 : list C) d1 d2,
    0 <= i < Zlength l1 ->
    Zlength l1 = Zlength l2 ->
    Znth i (combine l1 l2) (d1, d2) =
      (Znth i l1 d1, Znth i l2 d2).
Proof.
  intros B C i l1.
  revert i; induction l1 as [|b l1 IHl1]; intros.
  - rewrite Zlength_correct in H. simpl in H. lia.
  - destruct l2 as [|c l2].
    + rewrite !Zlength_correct in H0. simpl in H0. lia.
    + simpl.
      destruct (Z_le_lt_eq_dec 0 i ltac:(lia)) as [Hi | Hi].
      * rewrite (Znth_cons (d1, d2) i (b, c) (combine l1 l2)) by lia.
        rewrite (Znth_cons d1 i b l1) by lia.
        rewrite (Znth_cons d2 i c l2) by lia.
        apply IHl1.
        -- rewrite Zlength_correct in *. simpl in *. lia.
        -- rewrite !Zlength_correct in *. simpl in *. lia.
      * subst i.
        rewrite (Znth0_cons (d1, d2) (b, c) (combine l1 l2)).
        rewrite (Znth0_cons d1 b l1).
        rewrite (Znth0_cons d2 c l2).
        reflexivity.
Qed.
Lemma graph_rep_split__execution_representation :
  forall adjacency g row_ptrs node_addrs rows u,
    ZSimpleGraph.vertex_valid g u ->
    DFSAdjacencyList.graph_rep adjacency g row_ptrs node_addrs rows |--
      ((adjacency + u * sizeof (PTR)) # Ptr |-> Znth u row_ptrs 0) **
      DFSAdjacencyList.graph_except
        adjacency g row_ptrs node_addrs rows u **
      DFSAdjacencyList.addressed_sll
        (Znth u row_ptrs 0) (Znth u node_addrs nil) (Znth u rows nil).
Proof.
  intros adjacency g row_ptrs node_addrs rows u Hu.
  unfold DFSAdjacencyList.graph_rep,
    DFSAdjacencyList.linked_lists_rep,
    DFSAdjacencyList.graph_except,
    DFSAdjacencyList.list_blocks,
    DFSAdjacencyList.list_blocks_missing,
    DFSAdjacencyList.row_block.
  Intros.
  assert (Hptrs : Zlength row_ptrs = ZSimpleGraph.vertex_count g) by tauto.
  assert (Haddrs : Zlength node_addrs = ZSimpleGraph.vertex_count g) by tauto.
  assert (Hrows : Zlength rows = ZSimpleGraph.vertex_count g) by tauto.
  assert (Hi : 0 <= u < ZSimpleGraph.vertex_count g).
  { unfold ZSimpleGraph.vertex_valid in Hu. exact Hu. }
  assert (Hinner_len :
    Zlength (combine node_addrs rows) = ZSimpleGraph.vertex_count g).
  { rewrite (PtrPtrArray2.Zlength_combine_eq node_addrs rows).
    - exact Haddrs.
    - lia. }
  assert (Hcombine :
    0 <= u < Zlength (combine row_ptrs (combine node_addrs rows))).
  { assert (Houter_len :
      Zlength (combine row_ptrs (combine node_addrs rows)) =
      Zlength row_ptrs).
    { apply PtrPtrArray2.Zlength_combine_eq.
      exact (eq_trans Hptrs (eq_sym Hinner_len)). }
    rewrite Houter_len. change (0 <= u /\ u < Zlength row_ptrs).
    rewrite Hptrs. exact Hi. }
  sep_apply (PtrArray.full_split_to_missing_i adjacency u
    (ZSimpleGraph.vertex_count g) row_ptrs 0 Hi).
  sep_apply (iter_sepcon_split_remove_Znth__execution_representation
    DFSAdjacencyList.row_block
    u (combine row_ptrs (combine node_addrs rows))
    (0, (nil, nil)) Hcombine).
  assert (HZinner :
    Znth u (combine node_addrs rows) (nil, nil) =
      (Znth u node_addrs nil, Znth u rows nil)).
  { apply Znth_combine__execution_representation; lia. }
  assert (HZouter :
    Znth u (combine row_ptrs (combine node_addrs rows))
      (0, (nil, nil)) =
      (Znth u row_ptrs 0,
        Znth u (combine node_addrs rows) (nil, nil))).
  { apply Znth_combine__execution_representation.
    - change (0 <= u /\ u < Zlength row_ptrs).
      replace (Zlength row_ptrs) with (ZSimpleGraph.vertex_count g)
        by (symmetry; exact Hptrs).
      exact Hi.
    - exact (eq_trans Hptrs (eq_sym Hinner_len)). }
  rewrite HZouter, HZinner.
  cbn [fst snd].
  unfold DFSAdjacencyList.row_block.
  change (sizeof (PTR)) with ptr_size_Z.
  fold_arch.
  entailer!.
  all: try lia.
  all: entailer!.
Qed.
Lemma graph_rep_merge__execution_representation :
  forall adjacency g row_ptrs node_addrs rows u,
    ZSimpleGraph.vertex_valid g u ->
    ((adjacency + u * sizeof (PTR)) # Ptr |-> Znth u row_ptrs 0) **
    DFSAdjacencyList.graph_except
      adjacency g row_ptrs node_addrs rows u **
    DFSAdjacencyList.addressed_sll
      (Znth u row_ptrs 0) (Znth u node_addrs nil) (Znth u rows nil) |--
      DFSAdjacencyList.graph_rep adjacency g row_ptrs node_addrs rows.
Proof.
  intros adjacency g row_ptrs node_addrs rows u Hu.
  unfold DFSAdjacencyList.graph_rep,
    DFSAdjacencyList.linked_lists_rep,
    DFSAdjacencyList.graph_except,
    DFSAdjacencyList.list_blocks,
    DFSAdjacencyList.list_blocks_missing,
    DFSAdjacencyList.row_block.
  Intros.
  rename H into Hexcept.
  destruct Hexcept as [Hmodel [Hptrs [Haddrs [Hrows Hvalid]]]].
  assert (Hi : 0 <= u < ZSimpleGraph.vertex_count g).
  { unfold ZSimpleGraph.vertex_valid in Hu. exact Hu. }
  assert (Hinner_len :
    Zlength (combine node_addrs rows) = ZSimpleGraph.vertex_count g).
  { rewrite (PtrPtrArray2.Zlength_combine_eq node_addrs rows).
    - exact Haddrs.
    - lia. }
  assert (Hcombine :
    0 <= u < Zlength (combine row_ptrs (combine node_addrs rows))).
  { assert (Houter_len :
      Zlength (combine row_ptrs (combine node_addrs rows)) =
      Zlength row_ptrs).
    { apply PtrPtrArray2.Zlength_combine_eq.
      exact (eq_trans Hptrs (eq_sym Hinner_len)). }
    rewrite Houter_len. change (0 <= u /\ u < Zlength row_ptrs).
    replace (Zlength row_ptrs) with (ZSimpleGraph.vertex_count g)
      by (symmetry; exact Hptrs).
    exact Hi. }
  assert (HZinner :
    Znth u (combine node_addrs rows) (nil, nil) =
      (Znth u node_addrs nil, Znth u rows nil)).
  { apply Znth_combine__execution_representation; lia. }
  assert (HZouter :
    Znth u (combine row_ptrs (combine node_addrs rows))
      (0, (nil, nil)) =
      (Znth u row_ptrs 0,
        Znth u (combine node_addrs rows) (nil, nil))).
  { apply Znth_combine__execution_representation.
    - change (0 <= u /\ u < Zlength row_ptrs).
      replace (Zlength row_ptrs) with (ZSimpleGraph.vertex_count g)
        by (symmetry; exact Hptrs).
      exact Hi.
    - exact (eq_trans Hptrs (eq_sym Hinner_len)). }
  change (sizeof (PTR)) with ptr_size_Z.
  fold_arch.
  eapply derivable1_trans with
    (y :=
      ((((adjacency + u * ptr_size_Z) # Ptr |-> Znth u row_ptrs 0) **
        PtrArray.missing_i
          adjacency u 0 (ZSimpleGraph.vertex_count g) row_ptrs) **
       (iter_sepcon
          (map DFSAdjacencyList.row_block
            (PtrPtrArray2.remove_Znth u
              (combine row_ptrs (combine node_addrs rows)))) **
        DFSAdjacencyList.addressed_sll
          (Znth u row_ptrs 0) (Znth u node_addrs nil) (Znth u rows nil)))).
  { entailer!. }
  sep_apply (PtrArray.missing_i_merge_to_full adjacency u
    (ZSimpleGraph.vertex_count g) (Znth u row_ptrs 0) row_ptrs Hi).
  rewrite replace_Znth_Znth by lia.
  pose proof (PtrPtrArray2.iter_sepcon_merge_remove_Znth
    DFSAdjacencyList.row_block
    u (combine row_ptrs (combine node_addrs rows))
    (Znth u row_ptrs 0,
      (Znth u node_addrs nil, Znth u rows nil)) Hcombine)
    as Hmerge_lists.
  cbn [fst snd] in Hmerge_lists.
  assert (Horder_lists :
    iter_sepcon
      (map DFSAdjacencyList.row_block
        (PtrPtrArray2.remove_Znth u
          (combine row_ptrs (combine node_addrs rows)))) **
    DFSAdjacencyList.addressed_sll
      (Znth u row_ptrs 0) (Znth u node_addrs nil) (Znth u rows nil) |--
    DFSAdjacencyList.addressed_sll
      (Znth u row_ptrs 0) (Znth u node_addrs nil) (Znth u rows nil) **
    iter_sepcon
      (map DFSAdjacencyList.row_block
        (PtrPtrArray2.remove_Znth u
          (combine row_ptrs (combine node_addrs rows))))).
  { entailer!. }
  rewrite Horder_lists.
  rewrite Hmerge_lists.
  rewrite <- HZinner, <- HZouter.
  rewrite replace_Znth_Znth by exact Hcombine.
  entailer!.
Qed.
Lemma graph_except_model__execution_representation :
  forall adjacency g row_ptrs node_addrs rows u,
    DFSAdjacencyList.graph_except adjacency g row_ptrs node_addrs rows u |--
      “ DFSAdjacencyList.adjacency_lists_model g rows ”.
Proof.
  intros.
  unfold DFSAdjacencyList.graph_except.
  Intros.
  entailer!.
Qed.

Lemma addressed_sllseg_append__dfs_flow :
  forall x y z addrs1 addrs2 values1 values2,
    DFSAdjacencyList.addressed_sllseg x y addrs1 values1 **
    DFSAdjacencyList.addressed_sllseg y z addrs2 values2 |--
    DFSAdjacencyList.addressed_sllseg x z
      (addrs1 ++ addrs2) (values1 ++ values2).
Proof.
  intros x y z addrs1.
  revert x y z.
  induction addrs1 as [|node addrs1 IH];
    intros x y z addrs2 values1 values2;
    destruct values1 as [|datum values1]; simpl.
  - Intros_p Hxy. subst x. cancel.
  - entailer!.
  - entailer!.
  - Intros next.
    Exists next.
    split_pure_spatial.
    + cancel (&(node # "list" ->ₛ "data") # Int |-> datum).
      cancel (&(node # "list" ->ₛ "next") # Ptr |-> next).
      apply (IH next y z addrs2 values1 values2).
    + dump_pre_spatial. exact H.
Qed.
Lemma addressed_sllseg_sll__dfs_flow :
  forall x y addrs1 addrs2 values1 values2,
    DFSAdjacencyList.addressed_sllseg x y addrs1 values1 **
    DFSAdjacencyList.addressed_sll y addrs2 values2 |--
    DFSAdjacencyList.addressed_sll x
      (addrs1 ++ addrs2) (values1 ++ values2).
Proof.
  intros x y addrs1.
  revert x y.
  induction addrs1 as [|node addrs1 IH];
    intros x y addrs2 values1 values2;
    destruct values1 as [|datum values1]; simpl.
  - Intros_p Hxy. subst x. cancel.
  - entailer!.
  - entailer!.
  - Intros next.
    Exists next.
    split_pure_spatial.
    + cancel (&(node # "list" ->ₛ "data") # Int |-> datum).
      cancel (&(node # "list" ->ₛ "next") # Ptr |-> next).
      apply (IH next y addrs2 values1 values2).
    + dump_pre_spatial. exact H.
Qed.
Lemma addressed_sllseg_null_sll__dfs_flow :
  forall x addrs values,
    DFSAdjacencyList.addressed_sllseg x NULL addrs values |--
    DFSAdjacencyList.addressed_sll x addrs values.
Proof.
  intros x addrs.
  revert x.
  induction addrs as [|node addrs IH];
    intros x values; destruct values as [|datum values]; simpl.
  - entailer!.
  - entailer!.
  - entailer!.
  - Intros next.
    Exists next.
    split_pure_spatial.
    + cancel (&(node # "list" ->ₛ "data") # Int |-> datum).
      cancel (&(node # "list" ->ₛ "next") # Ptr |-> next).
      apply (IH next values).
    + dump_pre_spatial. exact H.
Qed.
Lemma addressed_sll_reverse_split__dfs_flow :
  forall x node prefix_addrs suffix_addrs prefix_values datum suffix_values,
    Zlength prefix_addrs = Zlength prefix_values ->
    DFSAdjacencyList.addressed_sll x
      (prefix_addrs ++ node :: suffix_addrs)
      (prefix_values ++ datum :: suffix_values) |--
    EX next,
      DFSAdjacencyList.addressed_sllseg x node
        prefix_addrs prefix_values **
      (&(node # "list" ->ₛ "data") # Int |-> datum) **
      (&(node # "list" ->ₛ "next") # Ptr |-> next) **
      DFSAdjacencyList.addressed_sll next suffix_addrs suffix_values.
Proof.
  intros x node prefix_addrs.
  revert x.
  induction prefix_addrs as [|head prefix_addrs IH];
    intros x suffix_addrs prefix_values datum suffix_values Hlen;
    destruct prefix_values as [|value prefix_values].
  - simpl. Intros next. Exists next. entailer!.
  - rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - assert (Htail : Zlength prefix_addrs = Zlength prefix_values).
    { rewrite !Zlength_correct in *. simpl in *. lia. }
    simpl DFSAdjacencyList.addressed_sll.
    Intros next.
    sep_apply (IH next suffix_addrs prefix_values datum suffix_values Htail).
    Intros tail_next.
    Exists tail_next.
    simpl DFSAdjacencyList.addressed_sllseg.
    Exists next.
    entailer!.
Qed.
