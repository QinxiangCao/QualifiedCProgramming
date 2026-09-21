Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import AUXLib.MonotonicList.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** A full binary prefix-code tree.  Leaves carry symbol frequencies and every
    internal constructor has exactly two children, so this datatype describes
    the genuine feasible tree space independently of the Huffman algorithm. *)
Inductive HuffmanTree : Type :=
  | HuffmanLeaf : Z -> HuffmanTree
  | HuffmanNode : HuffmanTree -> HuffmanTree -> HuffmanTree.

Fixpoint HuffmanLeaves (tree : HuffmanTree) : list Z :=
  match tree with
  | HuffmanLeaf weight => [weight]
  | HuffmanNode left_tree right_tree =>
      HuffmanLeaves left_tree ++ HuffmanLeaves right_tree
  end.

Fixpoint HuffmanTreeWeight (tree : HuffmanTree) : Z :=
  match tree with
  | HuffmanLeaf weight => weight
  | HuffmanNode left_tree right_tree =>
      HuffmanTreeWeight left_tree + HuffmanTreeWeight right_tree
  end.

(** Weighted external path length.  Joining two subtrees increases every leaf
    depth below the new root by one, hence adds both subtree weights. *)
Fixpoint HuffmanWeightedPathLength (tree : HuffmanTree) : Z :=
  match tree with
  | HuffmanLeaf _ => 0
  | HuffmanNode left_tree right_tree =>
      HuffmanWeightedPathLength left_tree +
      HuffmanWeightedPathLength right_tree +
      HuffmanTreeWeight left_tree + HuffmanTreeWeight right_tree
  end.

Definition HuffmanTreeFeasible
    (weights : list Z) (tree : HuffmanTree) : Prop :=
  Permutation weights (HuffmanLeaves tree).

(** Public mathematical result: [answer] is the minimum weighted external
    path length over all full binary trees with exactly the input leaf-weight
    multiset.  The minimization is deliberately the repository MaxMinLib
    interface, not a custom minimum relation or an algorithm-generated set. *)
Definition HuffmanOptimalCost
    (weights : list Z) (answer : Z) : Prop :=
  min_value_of_subset Z.le
    (HuffmanTreeFeasible weights)
    HuffmanWeightedPathLength
    answer.

(* Compatibility premise used only by the original internal arithmetic lemmas.
   Public annotations state both Forall bounds explicitly. *)
Definition HuffmanInputBounded (weights : list Z) : Prop :=
  forall i,
    0 <= i < Zlength weights ->
    1 <= Znth i weights 0 <= 1000.

(** The scratch array's only public value-level commitment: its surviving
    live root has the sum of all input frequencies.  Remaining cells are
    intentionally unconstrained. *)
Definition HuffmanScratchFinal
    (weights scratch : list Z) : Prop :=
  Znth 0 scratch 0 = sum weights.

(** Internal mathematical interface shared by the merge-loop phases.  It says
    that solving the current residual instance and adding the already charged
    merge cost gives a genuine optimum for the original input. *)
Definition HuffmanResidualOptimum
    (input live : list Z) (accumulated : Z) : Prop :=
  sum live = sum input /\
  exists remaining,
    HuffmanOptimalCost live remaining /\
    HuffmanOptimalCost input (accumulated + remaining).

Definition HuffmanProgress
    (input scratch : list Z) (active accumulated : Z) : Prop :=
  HuffmanResidualOptimum input (sublist 0 active scratch) accumulated.

(** Legacy proof compatibility below: these three predicates are used only
    in the existing internal lemmas. The public C interfaces at the end of this
    file use MaxMinLib and are connected by proved equivalences.

    [best] denotes a minimum of the already scanned prefix. Bounds for
    [best], [scanned], and concrete array access deliberately remain in C. *)
Definition HuffmanMinScanLegacy
    (scratch : list Z) (scanned best : Z) : Prop :=
  forall k,
    0 <= k < scanned ->
    Znth best scratch 0 <= Znth k scratch 0.

(** One globally minimum residual weight has been removed from scratch and is
    held in the local [held].  The remaining live prefix plus that value is
    the prior residual multiset. *)
Definition HuffmanFirstHeldLegacy
    (input scratch : list Z)
    (active held accumulated : Z) : Prop :=
  exists prior_live,
    Permutation prior_live (held :: sublist 0 active scratch) /\
    (forall weight, In weight prior_live -> held <= weight) /\
    HuffmanResidualOptimum input prior_live accumulated.

(** Both greedy-smallest values are held and [scratch[0..active)] is the rest
    of the prior residual multiset.  This is the implementation-independent
    premise of the Huffman greedy-choice theorem. *)
Definition HuffmanPairReadyLegacy
    (input scratch : list Z)
    (active first second accumulated : Z) : Prop :=
  exists prior_live,
    Permutation prior_live
      (first :: second :: sublist 0 active scratch) /\
    (forall weight, In weight prior_live -> first <= weight) /\
    (forall weight,
      In weight (second :: sublist 0 active scratch) -> second <= weight) /\
    HuffmanResidualOptimum input prior_live accumulated.

(** Proof-support infrastructure for the structural Huffman greedy-choice
    argument.  These declarations are intentionally independent of the C
    implementation and of the public [HuffmanOptimalCost] candidate space. *)

Fixpoint HuffmanTreeHeight (tree : HuffmanTree) : Z :=
  match tree with
  | HuffmanLeaf _ => 0
  | HuffmanNode left_tree right_tree =>
      Z.max (HuffmanTreeHeight left_tree)
        (HuffmanTreeHeight right_tree) + 1
  end.

Fixpoint HuffmanLeafDepths (tree : HuffmanTree) : list Z :=
  match tree with
  | HuffmanLeaf _ => [0]
  | HuffmanNode left_tree right_tree =>
      map (fun depth => depth + 1) (HuffmanLeafDepths left_tree) ++
      map (fun depth => depth + 1) (HuffmanLeafDepths right_tree)
  end.

(** A one-hole zipper context.  The recursive context lies between the hole
    and the constructor currently being recorded. *)
Inductive HuffmanTreeContext : Type :=
  | HuffmanRootContext : HuffmanTreeContext
  | HuffmanLeftContext :
      HuffmanTreeContext -> HuffmanTree -> HuffmanTreeContext
  | HuffmanRightContext :
      HuffmanTree -> HuffmanTreeContext -> HuffmanTreeContext.

Fixpoint HuffmanPlug
    (context : HuffmanTreeContext) (hole : HuffmanTree) : HuffmanTree :=
  match context with
  | HuffmanRootContext => hole
  | HuffmanLeftContext inner right_tree =>
      HuffmanNode (HuffmanPlug inner hole) right_tree
  | HuffmanRightContext left_tree inner =>
      HuffmanNode left_tree (HuffmanPlug inner hole)
  end.

Fixpoint HuffmanContextDepth (context : HuffmanTreeContext) : Z :=
  match context with
  | HuffmanRootContext => 0
  | HuffmanLeftContext inner _ => HuffmanContextDepth inner + 1
  | HuffmanRightContext _ inner => HuffmanContextDepth inner + 1
  end.

Fixpoint HuffmanContextLeaves
    (context : HuffmanTreeContext) (hole_leaves : list Z) : list Z :=
  match context with
  | HuffmanRootContext => hole_leaves
  | HuffmanLeftContext inner right_tree =>
      HuffmanContextLeaves inner hole_leaves ++ HuffmanLeaves right_tree
  | HuffmanRightContext left_tree inner =>
      HuffmanLeaves left_tree ++ HuffmanContextLeaves inner hole_leaves
  end.

Fixpoint HuffmanContextWeight
    (context : HuffmanTreeContext) (hole_weight : Z) : Z :=
  match context with
  | HuffmanRootContext => hole_weight
  | HuffmanLeftContext inner right_tree =>
      HuffmanContextWeight inner hole_weight +
        HuffmanTreeWeight right_tree
  | HuffmanRightContext left_tree inner =>
      HuffmanTreeWeight left_tree +
        HuffmanContextWeight inner hole_weight
  end.

Fixpoint HuffmanContextPathLength
    (context : HuffmanTreeContext)
    (hole_weight hole_path_length : Z) : Z :=
  match context with
  | HuffmanRootContext => hole_path_length
  | HuffmanLeftContext inner right_tree =>
      HuffmanContextPathLength inner hole_weight hole_path_length +
      HuffmanWeightedPathLength right_tree +
      HuffmanContextWeight inner hole_weight +
      HuffmanTreeWeight right_tree
  | HuffmanRightContext left_tree inner =>
      HuffmanWeightedPathLength left_tree +
      HuffmanContextPathLength inner hole_weight hole_path_length +
      HuffmanTreeWeight left_tree +
      HuffmanContextWeight inner hole_weight
  end.

Definition HuffmanWeightedDepths
    (weights depths : list Z) : Z :=
  sum
    (map (fun pair : Z * Z => fst pair * snd pair)
      (combine weights depths)).

Definition HuffmanDeepestSibling
    (tree : HuffmanTree) (context : HuffmanTreeContext)
    (left_weight right_weight : Z) : Prop :=
  tree = HuffmanPlug context
    (HuffmanNode
      (HuffmanLeaf left_weight) (HuffmanLeaf right_weight)) /\
  HuffmanContextDepth context + 1 = HuffmanTreeHeight tree.

Definition HuffmanContractSibling
    (context : HuffmanTreeContext)
    (left_weight right_weight : Z) : HuffmanTree :=
  HuffmanPlug context (HuffmanLeaf (left_weight + right_weight)).

Lemma huffman_tree_weight_leaves :
  forall tree,
    HuffmanTreeWeight tree = sum (HuffmanLeaves tree).
Proof.
  intros tree.
  induction tree; simpl; rewrite ?sum_app; lia.
Qed.

Lemma huffman_weighted_depths_app :
  forall weights1 weights2 depths1 depths2,
    length weights1 = length depths1 ->
    HuffmanWeightedDepths
      (weights1 ++ weights2) (depths1 ++ depths2) =
    HuffmanWeightedDepths weights1 depths1 +
      HuffmanWeightedDepths weights2 depths2.
Proof.
  unfold HuffmanWeightedDepths.
  intros weights1.
  induction weights1 as [|weight weights1 IH];
    intros weights2 depths1 depths2 Hlength.
  - destruct depths1; [reflexivity|discriminate].
  - destruct depths1 as [|depth depths1]; [discriminate|].
    simpl in Hlength |- *.
    apply Nat.succ_inj in Hlength.
    rewrite IH by exact Hlength.
    lia.
Qed.

Lemma huffman_weighted_depths_lift :
  forall weights depths,
    length weights = length depths ->
    HuffmanWeightedDepths weights (map (fun depth => depth + 1) depths) =
      HuffmanWeightedDepths weights depths + sum weights.
Proof.
  unfold HuffmanWeightedDepths.
  intros weights.
  induction weights as [|weight weights IH]; intros depths Hlength.
  - destruct depths; [reflexivity|discriminate].
  - destruct depths as [|depth depths]; [discriminate|].
    simpl in Hlength |- *.
    apply Nat.succ_inj in Hlength.
    rewrite IH by exact Hlength.
    lia.
Qed.

Lemma huffman_leaf_depth_profile :
  forall tree,
    length (HuffmanLeaves tree) = length (HuffmanLeafDepths tree) /\
    HuffmanWeightedDepths
      (HuffmanLeaves tree) (HuffmanLeafDepths tree) =
      HuffmanWeightedPathLength tree.
Proof.
  intros tree.
  induction tree as [weight|left IHleft right IHright].
  - simpl. split; [reflexivity|].
    unfold HuffmanWeightedDepths. cbn. lia.
  - destruct IHleft as [Hleft_length Hleft_cost].
    destruct IHright as [Hright_length Hright_cost].
    simpl HuffmanLeaves.
    simpl HuffmanLeafDepths.
    split.
    + rewrite !length_app, !length_map, Hleft_length, Hright_length.
      reflexivity.
    + rewrite huffman_weighted_depths_app.
      2:{ rewrite length_map. exact Hleft_length. }
      rewrite huffman_weighted_depths_lift by exact Hleft_length.
      rewrite huffman_weighted_depths_lift by exact Hright_length.
      rewrite Hleft_cost, Hright_cost.
      rewrite <- !huffman_tree_weight_leaves.
      simpl. lia.
Qed.

Lemma huffman_leaf_depths_bounded :
  forall tree,
    Forall
      (fun depth => depth <= HuffmanTreeHeight tree)
      (HuffmanLeafDepths tree).
Proof.
  intros tree.
  induction tree as [weight|left IHleft right IHright].
  - simpl. constructor; [lia|constructor].
  - simpl.
    apply Forall_app.
    split.
    + rewrite Forall_forall in IHleft |- *.
      intros depth Hin.
      apply in_map_iff in Hin.
      destruct Hin as [old_depth [Heq Hin]].
      subst depth.
      specialize (IHleft old_depth Hin).
      pose proof (Z.le_max_l
        (HuffmanTreeHeight left) (HuffmanTreeHeight right)).
      lia.
    + rewrite Forall_forall in IHright |- *.
      intros depth Hin.
      apply in_map_iff in Hin.
      destruct Hin as [old_depth [Heq Hin]].
      subst depth.
      specialize (IHright old_depth Hin).
      pose proof (Z.le_max_r
        (HuffmanTreeHeight left) (HuffmanTreeHeight right)).
      lia.
Qed.

Lemma huffman_tree_height_nonnegative :
  forall tree, 0 <= HuffmanTreeHeight tree.
Proof.
  intros tree.
  induction tree; simpl.
  - lia.
  - pose proof (Z.le_max_l
      (HuffmanTreeHeight tree1) (HuffmanTreeHeight tree2)).
    lia.
Qed.

Lemma huffman_plug_leaves :
  forall context hole,
    HuffmanLeaves (HuffmanPlug context hole) =
      HuffmanContextLeaves context (HuffmanLeaves hole).
Proof.
  intros context.
  induction context; intros hole; simpl; rewrite ?IHcontext; reflexivity.
Qed.

Lemma huffman_plug_weight :
  forall context hole,
    HuffmanTreeWeight (HuffmanPlug context hole) =
      HuffmanContextWeight context (HuffmanTreeWeight hole).
Proof.
  intros context.
  induction context; intros hole; simpl; rewrite ?IHcontext; reflexivity.
Qed.

Lemma huffman_plug_path_length :
  forall context hole,
    HuffmanWeightedPathLength (HuffmanPlug context hole) =
      HuffmanContextPathLength context
        (HuffmanTreeWeight hole) (HuffmanWeightedPathLength hole).
Proof.
  intros context.
  induction context; intros hole; simpl;
    rewrite ?IHcontext, ?huffman_plug_weight; reflexivity.
Qed.

Lemma huffman_context_leaves_permutation :
  forall context first_leaves second_leaves,
    Permutation first_leaves second_leaves ->
    Permutation
      (HuffmanContextLeaves context first_leaves)
      (HuffmanContextLeaves context second_leaves).
Proof.
  intros context.
  induction context; intros first_leaves second_leaves Hperm; simpl.
  - exact Hperm.
  - apply Permutation_app; [apply IHcontext; exact Hperm|reflexivity].
  - apply Permutation_app; [reflexivity|apply IHcontext; exact Hperm].
Qed.

Lemma huffman_plug_leaves_permutation :
  forall context first_tree second_tree,
    Permutation (HuffmanLeaves first_tree) (HuffmanLeaves second_tree) ->
    Permutation
      (HuffmanLeaves (HuffmanPlug context first_tree))
      (HuffmanLeaves (HuffmanPlug context second_tree)).
Proof.
  intros context first_tree second_tree Hperm.
  rewrite !huffman_plug_leaves.
  apply huffman_context_leaves_permutation.
  exact Hperm.
Qed.

Lemma huffman_context_path_length_shift :
  forall context hole_weight hole_path_length increment,
    HuffmanContextPathLength context hole_weight
      (hole_path_length + increment) =
    HuffmanContextPathLength context hole_weight hole_path_length +
      increment.
Proof.
  intros context.
  induction context;
    intros hole_weight hole_path_length increment; simpl.
  - lia.
  - rewrite IHcontext. lia.
  - rewrite IHcontext. lia.
Qed.

Lemma huffman_deepest_sibling_exists :
  forall tree,
    (exists left_tree right_tree,
      tree = HuffmanNode left_tree right_tree) ->
    exists context left_weight right_weight,
      HuffmanDeepestSibling
        tree context left_weight right_weight.
Proof.
  intros tree.
  induction tree as [weight|left IHleft right IHright]; intros Hnode.
  - destruct Hnode as [left_tree [right_tree Hfalse]]. discriminate.
  - destruct left as [left_weight|left_left left_right];
      destruct right as [right_weight|right_left right_right].
    + exists HuffmanRootContext, left_weight, right_weight.
      split; reflexivity.
    + destruct (IHright (ex_intro _ right_left
        (ex_intro _ right_right eq_refl))) as
        [context [first_weight [second_weight [Hshape Hdepth]]]].
      exists (HuffmanRightContext (HuffmanLeaf left_weight) context),
        first_weight, second_weight.
      split.
      * simpl. rewrite <- Hshape. reflexivity.
      * change
          (HuffmanContextDepth context + 1 =
            HuffmanTreeHeight
              (HuffmanNode right_left right_right)) in Hdepth.
        change
          (HuffmanContextDepth context + 1 + 1 =
            Z.max 0
              (HuffmanTreeHeight
                (HuffmanNode right_left right_right)) + 1).
        rewrite Hdepth.
        rewrite Z.max_r; [reflexivity|].
        apply huffman_tree_height_nonnegative.
    + destruct (IHleft (ex_intro _ left_left
        (ex_intro _ left_right eq_refl))) as
        [context [first_weight [second_weight [Hshape Hdepth]]]].
      exists (HuffmanLeftContext context (HuffmanLeaf right_weight)),
        first_weight, second_weight.
      split.
      * simpl. rewrite <- Hshape. reflexivity.
      * change
          (HuffmanContextDepth context + 1 =
            HuffmanTreeHeight
              (HuffmanNode left_left left_right)) in Hdepth.
        change
          (HuffmanContextDepth context + 1 + 1 =
            Z.max
              (HuffmanTreeHeight
                (HuffmanNode left_left left_right)) 0 + 1).
        rewrite Hdepth.
        rewrite Z.max_l; [reflexivity|].
        apply huffman_tree_height_nonnegative.
    + destruct (Z_le_dec
        (HuffmanTreeHeight (HuffmanNode left_left left_right))
        (HuffmanTreeHeight (HuffmanNode right_left right_right)))
        as [Hle|Hnotle].
      * destruct (IHright (ex_intro _ right_left
          (ex_intro _ right_right eq_refl))) as
          [context [first_weight [second_weight [Hshape Hdepth]]]].
        exists
          (HuffmanRightContext
            (HuffmanNode left_left left_right) context),
          first_weight, second_weight.
        split.
        -- simpl. rewrite <- Hshape. reflexivity.
        -- change
             (HuffmanContextDepth context + 1 =
               HuffmanTreeHeight
                 (HuffmanNode right_left right_right)) in Hdepth.
           change
             (HuffmanContextDepth context + 1 + 1 =
               Z.max
                 (HuffmanTreeHeight
                   (HuffmanNode left_left left_right))
                 (HuffmanTreeHeight
                   (HuffmanNode right_left right_right)) + 1).
           rewrite Hdepth, Z.max_r by exact Hle.
           reflexivity.
      * assert (Hge :
          HuffmanTreeHeight (HuffmanNode right_left right_right) <=
          HuffmanTreeHeight (HuffmanNode left_left left_right)) by lia.
        destruct (IHleft (ex_intro _ left_left
          (ex_intro _ left_right eq_refl))) as
          [context [first_weight [second_weight [Hshape Hdepth]]]].
        exists
          (HuffmanLeftContext context
            (HuffmanNode right_left right_right)),
          first_weight, second_weight.
        split.
        -- simpl. rewrite <- Hshape. reflexivity.
        -- change
             (HuffmanContextDepth context + 1 =
               HuffmanTreeHeight
                 (HuffmanNode left_left left_right)) in Hdepth.
           change
             (HuffmanContextDepth context + 1 + 1 =
               Z.max
                 (HuffmanTreeHeight
                   (HuffmanNode left_left left_right))
                 (HuffmanTreeHeight
                   (HuffmanNode right_left right_right)) + 1).
           rewrite Hdepth, Z.max_l by exact Hge.
           reflexivity.
Qed.

Lemma permutation_two_across_prefix :
  forall (A : Type) (prefix suffix : list A) first second,
    Permutation
      (prefix ++ first :: second :: suffix)
      (first :: second :: prefix ++ suffix).
Proof.
  intros A prefix suffix first second.
  replace (prefix ++ first :: second :: suffix)
    with ((prefix ++ [first; second]) ++ suffix).
  2:{ rewrite <- app_assoc. reflexivity. }
  replace (first :: second :: prefix ++ suffix)
    with (([first; second] ++ prefix) ++ suffix).
  2:{ rewrite <- app_assoc. reflexivity. }
  apply Permutation_app_tail.
  apply Permutation_app_comm.
Qed.

Lemma huffman_context_pair_depths :
  forall context left_weight right_weight,
    exists other_depths,
      Permutation
        (HuffmanLeafDepths
          (HuffmanPlug context
            (HuffmanNode
              (HuffmanLeaf left_weight) (HuffmanLeaf right_weight))))
        ((HuffmanContextDepth context + 1) ::
          (HuffmanContextDepth context + 1) :: other_depths).
Proof.
  intros context.
  induction context as
      [|inner IHinner right_tree|left_tree inner IHinner];
    intros left_weight right_weight.
  - exists []. simpl. reflexivity.
  - destruct (IHinner left_weight right_weight) as
      [other_depths Hperm].
    exists
      (map (fun depth => depth + 1) other_depths ++
        map (fun depth => depth + 1)
          (HuffmanLeafDepths right_tree)).
    simpl.
    change (Permutation
      (map (fun depth : Z => depth + 1)
          (HuffmanLeafDepths
            (HuffmanPlug inner
              (HuffmanNode
                (HuffmanLeaf left_weight) (HuffmanLeaf right_weight)))) ++
        map (fun depth : Z => depth + 1)
          (HuffmanLeafDepths right_tree))
      (((HuffmanContextDepth inner + 1 + 1) ::
        (HuffmanContextDepth inner + 1 + 1) ::
        map (fun depth : Z => depth + 1) other_depths) ++
        map (fun depth : Z => depth + 1)
          (HuffmanLeafDepths right_tree))).
    apply Permutation_app.
    + change (Permutation
        (map (fun depth : Z => depth + 1)
          (HuffmanLeafDepths
            (HuffmanPlug inner
              (HuffmanNode
                (HuffmanLeaf left_weight) (HuffmanLeaf right_weight)))))
        (map (fun depth : Z => depth + 1)
          ((HuffmanContextDepth inner + 1) ::
            (HuffmanContextDepth inner + 1) :: other_depths))).
      apply Permutation_map. exact Hperm.
    + reflexivity.
  - destruct (IHinner left_weight right_weight) as
      [other_depths Hperm].
    exists
      (map (fun depth => depth + 1) (HuffmanLeafDepths left_tree) ++
        map (fun depth => depth + 1) other_depths).
    simpl.
    eapply Permutation_trans.
    + apply Permutation_app; [reflexivity|].
      apply Permutation_map. exact Hperm.
    + apply permutation_two_across_prefix.
Qed.

Lemma huffman_deepest_sibling_profile :
  forall tree,
    (exists left_tree right_tree,
      tree = HuffmanNode left_tree right_tree) ->
    exists context left_weight right_weight other_depths,
      HuffmanDeepestSibling tree context left_weight right_weight /\
      Permutation (HuffmanLeafDepths tree)
        (HuffmanTreeHeight tree ::
          HuffmanTreeHeight tree :: other_depths) /\
      Forall
        (fun depth => depth <= HuffmanTreeHeight tree)
        (HuffmanLeafDepths tree).
Proof.
  intros tree Hnode.
  destruct (huffman_deepest_sibling_exists tree Hnode) as
    [context [left_weight [right_weight Hdeepest]]].
  destruct Hdeepest as [Hshape Hdepth].
  destruct (huffman_context_pair_depths
    context left_weight right_weight) as [other_depths Hperm].
  exists context, left_weight, right_weight, other_depths.
  split.
  - split; assumption.
  - split.
    + rewrite <- Hdepth.
      rewrite Hshape. exact Hperm.
    + apply huffman_leaf_depths_bounded.
Qed.

Lemma huffman_contract_leaves :
  forall context left_weight right_weight,
    HuffmanLeaves
      (HuffmanContractSibling context left_weight right_weight) =
    HuffmanContextLeaves context [left_weight + right_weight].
Proof.
  intros context left_weight right_weight.
  unfold HuffmanContractSibling.
  rewrite huffman_plug_leaves. reflexivity.
Qed.

Lemma huffman_expanded_sibling_leaves :
  forall context left_weight right_weight,
    HuffmanLeaves
      (HuffmanPlug context
        (HuffmanNode
          (HuffmanLeaf left_weight) (HuffmanLeaf right_weight))) =
    HuffmanContextLeaves context [left_weight; right_weight].
Proof.
  intros context left_weight right_weight.
  rewrite huffman_plug_leaves. reflexivity.
Qed.

Lemma huffman_contract_weight :
  forall context left_weight right_weight,
    HuffmanTreeWeight
      (HuffmanPlug context
        (HuffmanNode
          (HuffmanLeaf left_weight) (HuffmanLeaf right_weight))) =
    HuffmanTreeWeight
      (HuffmanContractSibling context left_weight right_weight).
Proof.
  intros context left_weight right_weight.
  unfold HuffmanContractSibling.
  rewrite !huffman_plug_weight. simpl. reflexivity.
Qed.

Lemma huffman_contract_path_length :
  forall context left_weight right_weight,
    HuffmanWeightedPathLength
      (HuffmanPlug context
        (HuffmanNode
          (HuffmanLeaf left_weight) (HuffmanLeaf right_weight))) =
    HuffmanWeightedPathLength
      (HuffmanContractSibling context left_weight right_weight) +
      left_weight + right_weight.
Proof.
  intros context left_weight right_weight.
  unfold HuffmanContractSibling.
  rewrite !huffman_plug_path_length. simpl.
  change
    (HuffmanContextPathLength context
      (left_weight + right_weight) (left_weight + right_weight) =
    HuffmanContextPathLength context
      (left_weight + right_weight) 0 + left_weight + right_weight).
  replace
    (HuffmanContextPathLength context
      (left_weight + right_weight) 0 + left_weight + right_weight)
    with
    (HuffmanContextPathLength context
      (left_weight + right_weight) 0 + (left_weight + right_weight))
    by lia.
  rewrite <- (huffman_context_path_length_shift context
    (left_weight + right_weight) 0 (left_weight + right_weight)).
  f_equal.
Qed.

Lemma huffman_deepest_sibling_contraction :
  forall tree context left_weight right_weight,
    HuffmanDeepestSibling tree context left_weight right_weight ->
    tree = HuffmanPlug context
      (HuffmanNode
        (HuffmanLeaf left_weight) (HuffmanLeaf right_weight)) /\
    HuffmanLeaves
      (HuffmanContractSibling context left_weight right_weight) =
      HuffmanContextLeaves context [left_weight + right_weight] /\
    HuffmanTreeWeight tree =
      HuffmanTreeWeight
        (HuffmanContractSibling context left_weight right_weight) /\
    HuffmanWeightedPathLength tree =
      HuffmanWeightedPathLength
        (HuffmanContractSibling context left_weight right_weight) +
      left_weight + right_weight.
Proof.
  intros tree context left_weight right_weight [Hshape Hdepth].
  split; [exact Hshape|].
  split; [apply huffman_contract_leaves|].
  split.
  - rewrite Hshape. apply huffman_contract_weight.
  - rewrite Hshape. apply huffman_contract_path_length.
Qed.

Lemma huffman_feasible_tree_exists__copy_initialization :
  forall weights,
    weights <> [] ->
    exists tree, HuffmanTreeFeasible weights tree.
Proof.
  induction weights as [| weight tail IH]; intros Hnonempty.
  - contradiction.
  - destruct tail as [| next rest].
    + exists (HuffmanLeaf weight).
      unfold HuffmanTreeFeasible.
      apply Permutation_refl.
    + destruct (IH ltac:(discriminate)) as [tail_tree Htail_tree].
      exists (HuffmanNode (HuffmanLeaf weight) tail_tree).
      unfold HuffmanTreeFeasible in *.
      simpl.
      apply perm_skip.
      exact Htail_tree.
Qed.
Lemma huffman_tree_cost_nonnegative__copy_initialization :
  forall tree,
    Forall (fun weight => 0 <= weight) (HuffmanLeaves tree) ->
    0 <= HuffmanTreeWeight tree /\
    0 <= HuffmanWeightedPathLength tree.
Proof.
  induction tree as [weight | left_tree IHleft right_tree IHright];
    intros Hweights.
  - inversion Hweights; subst; simpl; lia.
  - simpl in Hweights.
    apply Forall_app in Hweights.
    destruct Hweights as [Hleft Hright].
    specialize (IHleft Hleft).
    specialize (IHright Hright).
    simpl.
    lia.
Qed.
Lemma huffman_optimal_cost_exists__copy_initialization :
  forall weights,
    weights <> [] ->
    HuffmanInputBounded weights ->
    exists answer, HuffmanOptimalCost weights answer.
Proof.
  intros weights Hnonempty Hbounded.
  assert (Hweights_nonnegative:
    Forall (fun weight => 0 <= weight) weights).
  {
    apply Forall_forall.
    intros weight Hweight_in.
    destruct (In_nth weights weight 0 Hweight_in)
      as [index [Hindex Hweight]].
    specialize (Hbounded (Z.of_nat index)).
    assert (Hindex_Z:
      0 <= Z.of_nat index < Zlength weights).
    {
      rewrite Zlength_correct.
      lia.
    }
    specialize (Hbounded Hindex_Z).
    unfold Znth in Hbounded.
    rewrite Nat2Z.id in Hbounded.
    rewrite Hweight in Hbounded.
    lia.
  }
  destruct
    (huffman_feasible_tree_exists__copy_initialization weights Hnonempty)
    as [initial_tree Hinitial_feasible].
  assert (Hinitial_nonnegative:
    0 <= HuffmanWeightedPathLength initial_tree).
  {
    assert (Hinitial_weights:
      Forall (fun weight => 0 <= weight) (HuffmanLeaves initial_tree)).
    {
      unfold HuffmanTreeFeasible in Hinitial_feasible.
      eapply Permutation_Forall.
      - exact Hinitial_feasible.
      - exact Hweights_nonnegative.
    }
    pose proof
      (huffman_tree_cost_nonnegative__copy_initialization
        initial_tree) as Htree.
    apply Htree.
    exact Hinitial_weights.
  }
  pose proof
    (min_n_in_range
      (fun cost => exists tree,
        HuffmanTreeFeasible weights tree /\
        HuffmanWeightedPathLength tree = cost)
      (HuffmanWeightedPathLength initial_tree)
      Hinitial_nonnegative) as Hminimum.
  assert (Hexists_in_range:
    exists cost,
      0 <= cost <= HuffmanWeightedPathLength initial_tree /\
      (exists tree,
        HuffmanTreeFeasible weights tree /\
        HuffmanWeightedPathLength tree = cost)).
  {
    exists (HuffmanWeightedPathLength initial_tree).
    split.
    - lia.
    - exists initial_tree.
      split; [exact Hinitial_feasible | reflexivity].
  }
  specialize (Hminimum Hexists_in_range).
  destruct Hminimum as
    [answer [[tree [Htree_feasible Htree_cost]]
      [[Hanswer_nonnegative Hanswer_bounded] Hanswer_minimal]]].
  exists answer.
  unfold HuffmanOptimalCost, min_value_of_subset, min_object_of_subset.
  exists tree.
  split.
  - split.
    + exact Htree_feasible.
    + intros candidate Hcandidate_feasible.
      assert (Hcandidate_weights:
        Forall (fun weight => 0 <= weight) (HuffmanLeaves candidate)).
      {
        eapply Permutation_Forall.
        - exact Hcandidate_feasible.
        - exact Hweights_nonnegative.
      }
      pose proof
        (huffman_tree_cost_nonnegative__copy_initialization
          candidate Hcandidate_weights) as Hcandidate_nonnegative.
      destruct Hcandidate_nonnegative as [_ Hcandidate_nonnegative].
      rewrite Htree_cost.
      destruct (Z_le_gt_dec
        (HuffmanWeightedPathLength candidate)
        (HuffmanWeightedPathLength initial_tree)) as
        [Hcandidate_bounded | Hcandidate_large].
      * apply Hanswer_minimal.
        -- lia.
        -- exists candidate.
           split; [exact Hcandidate_feasible | reflexivity].
      * lia.
  - exact Htree_cost.
Qed.
Lemma huffman_initial_progress__copy_initialization :
  forall weights,
    1 <= Zlength weights ->
    HuffmanInputBounded weights ->
    HuffmanProgress weights weights (Zlength weights) 0.
Proof.
  intros weights Hlength Hbounded.
  unfold HuffmanProgress.
  rewrite (sublist_self weights (Zlength weights)) by reflexivity.
  unfold HuffmanResidualOptimum.
  split; [reflexivity |].
  assert (Hnonempty: weights <> []).
  {
    intros Heq.
    subst weights.
    rewrite Zlength_nil in Hlength.
    lia.
  }
  destruct
    (huffman_optimal_cost_exists__copy_initialization
      weights Hnonempty Hbounded) as [remaining Hoptimal].
  exists remaining.
  split; [exact Hoptimal |].
  replace (0 + remaining) with remaining by lia.
  exact Hoptimal.
Qed.
Lemma huffman_input_live_bounds__copy_initialization :
  forall weights n,
    Zlength weights = n ->
    HuffmanInputBounded weights ->
    forall k,
      0 <= k < n ->
      1 <= Znth k weights 0 <= 8000.
Proof.
  intros weights n Hlength Hbounded k Hk.
  specialize (Hbounded k).
  rewrite Hlength in Hbounded.
  specialize (Hbounded Hk).
  lia.
Qed.
Lemma huffman_min_scan_init__min_scan_updates :
  forall scratch,
    HuffmanMinScanLegacy scratch 1 0.
Proof.
  intros scratch k [Hnonnegative Hbelow_one].
  assert (k = 0) by lia.
  subst k.
  lia.
Qed.
Lemma huffman_min_scan_take_new__min_scan_updates :
  forall scratch scanned best,
    HuffmanMinScanLegacy scratch scanned best ->
    Znth scanned scratch 0 < Znth best scratch 0 ->
    HuffmanMinScanLegacy scratch (scanned + 1) scanned.
Proof.
  intros scratch scanned best Hscan Hnew k [Hnonnegative Hbelow_next].
  destruct (Z.lt_ge_cases k scanned) as [Hbelow | Hat_or_above].
  - specialize (Hscan k).
    lia.
  - assert (k = scanned) by lia.
    subst k.
    lia.
Qed.
Lemma huffman_min_scan_keep_old__min_scan_updates :
  forall scratch scanned best,
    HuffmanMinScanLegacy scratch scanned best ->
    Znth best scratch 0 <= Znth scanned scratch 0 ->
    HuffmanMinScanLegacy scratch (scanned + 1) best.
Proof.
  intros scratch scanned best Hscan Hnew k [Hnonnegative Hbelow_next].
  destruct (Z.lt_ge_cases k scanned) as [Hbelow | Hat_or_above].
  - apply Hscan.
    lia.
  - assert (k = scanned) by lia.
    subst k.
    exact Hnew.
Qed.
Lemma replace_last_removal_permutation__removals_bounds :
  forall (xs : list Z) selected active,
    0 <= selected < active ->
    active <= Zlength xs ->
    Permutation (sublist 0 active xs)
      (Znth selected xs 0 ::
       sublist 0 (active - 1)
         (replace_Znth selected (Znth (active - 1) xs 0) xs)).
Proof.
  induction xs as [|x xs IH]; intros selected active Hselected Hactive.
  - rewrite Zlength_nil in Hactive. lia.
  - destruct (Z.eq_dec selected 0) as [-> | Hselected_nonzero].
    + destruct (Z.eq_dec active 1) as [-> | Hactive_nonone].
      * change (Permutation [x] [x]). reflexivity.
      * assert (1 < active) by lia.
        rewrite sublist_cons1 by lia.
        rewrite Znth0_cons.
        change
          (replace_Znth 0 (Znth (active - 1) (x :: xs) 0) (x :: xs))
          with (Znth (active - 1) (x :: xs) 0 :: xs).
        rewrite sublist_cons1 by lia.
        rewrite Znth_cons by lia.
        rewrite (sublist_split 0 (active - 1) (active - 2) xs)
          by (rewrite Zlength_cons in Hactive; lia).
        replace (active - 1) with (active - 2 + 1) by lia.
        rewrite (sublist_single 0 (active - 2) xs)
          by (rewrite Zlength_cons in Hactive; lia).
        replace (active - 2 + 1 - 1) with (active - 2) by lia.
        apply perm_skip.
        apply Permutation_app_comm.
    + assert (0 < selected) by lia.
      assert (1 < active) by lia.
      rewrite sublist_cons1 by lia.
      rewrite Znth_cons by lia.
      rewrite replace_Znth_cons by lia.
      rewrite sublist_cons1 by lia.
      rewrite Znth_cons by lia.
      eapply Permutation_trans.
      * apply perm_skip.
        apply (IH (selected - 1) (active - 1)).
        -- lia.
        -- rewrite Zlength_cons in Hactive. lia.
      * apply perm_swap.
Qed.
Lemma replace_last_live_bounds__removals_bounds :
  forall (xs : list Z) selected active lower upper,
    0 <= selected < active ->
    active <= Zlength xs ->
    (forall k, 0 <= k < active ->
       lower <= Znth k xs 0 <= upper) ->
    forall k, 0 <= k < active - 1 ->
      lower <=
        Znth k
          (replace_Znth selected (Znth (active - 1) xs 0) xs) 0
      <= upper.
Proof.
  intros xs selected active lower upper Hselected Hactive Hbounds k Hk.
  destruct (Z.eq_dec k selected) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by lia.
    apply Hbounds. lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Hbounds. lia.
Qed.
Lemma huffman_first_held_after_removal__removals_bounds :
  forall input xs selected active accumulated,
    0 <= selected < active ->
    active <= Zlength xs ->
    HuffmanMinScanLegacy xs active selected ->
    HuffmanResidualOptimum input (sublist 0 active xs) accumulated ->
    HuffmanFirstHeldLegacy input
      (replace_Znth selected (Znth (active - 1) xs 0) xs)
      (active - 1) (Znth selected xs 0) accumulated.
Proof.
  intros input xs selected active accumulated
    Hselected Hactive Hminimum Hresidual.
  unfold HuffmanFirstHeldLegacy.
  exists (sublist 0 active xs).
  split.
  - apply replace_last_removal_permutation__removals_bounds; assumption.
  - split.
    + intros weight Hin.
      destruct (In_nth _ _ 0 Hin) as [k [Hk Hweight]].
      assert (Hprefix_length : Zlength (sublist 0 active xs) = active).
      { rewrite Zlength_sublist by lia. lia. }
      assert (HkZ : 0 <= Z.of_nat k < active).
      { rewrite <- Hprefix_length, Zlength_correct. lia. }
      specialize (Hminimum (Z.of_nat k) HkZ).
      assert
        (HweightZ :
           Znth (Z.of_nat k) (sublist 0 active xs) 0 = weight).
      { unfold Znth. rewrite Nat2Z.id. exact Hweight. }
      rewrite Znth_sublist0 in HweightZ by lia.
      rewrite HweightZ in Hminimum.
      exact Hminimum.
    + exact Hresidual.
Qed.
Lemma in_sublist0_has_index__removals_bounds :
  forall (A : Type) (l : list A) (d value : A) (active : Z),
    0 <= active <= Zlength l ->
    In value (sublist 0 active l) ->
    exists k, 0 <= k < active /\ Znth k l d = value.
Proof.
  intros A l d value active Hactive Hin.
  destruct (In_nth (sublist 0 active l) value d Hin)
    as [k [Hk Hvalue]].
  exists (Z.of_nat k).
  split.
  - pose proof (Zlength_sublist0 active l Hactive) as Hlen.
    rewrite Zlength_correct in Hlen.
    lia.
  - rewrite <- Hvalue.
    rewrite <- (Znth_sublist0 d (Z.of_nat k) active l) at 1 by
      (pose proof (Zlength_sublist0 active l Hactive) as Hlen;
       rewrite Zlength_correct in Hlen; lia).
    unfold Znth.
    rewrite Nat2Z.id.
    reflexivity.
Qed.
Lemma huffman_pair_ready_after_removal__removals_bounds :
  forall input scratch active held selected accumulated scanned n,
    Zlength scratch = n ->
    1 <= active < n ->
    0 <= selected < scanned ->
    active <= scanned <= active ->
    HuffmanFirstHeldLegacy input scratch active held accumulated ->
    HuffmanMinScanLegacy scratch scanned selected ->
    HuffmanPairReadyLegacy input
      (replace_Znth selected (Znth (active - 1) scratch 0) scratch)
      (active - 1) held (Znth selected scratch 0) accumulated.
Proof.
  intros input scratch active held selected accumulated scanned n
    Hlength Hactive Hselected Hscanned Hheld Hscan.
  assert (scanned = active) by lia. subst scanned.
  destruct Hheld as
    [prior_live [Hprior [Hheld_le Hresidual]]].
  assert (0 <= selected < active) as Hselected_active by lia.
  assert (active <= Zlength scratch) as Hactive_length by lia.
  pose proof
    (replace_last_removal_permutation__removals_bounds
      scratch selected active Hselected_active Hactive_length)
    as Hremove.
  exists prior_live.
  split.
  - eapply Permutation_trans; [exact Hprior|].
    apply perm_skip. exact Hremove.
  - split; [exact Hheld_le|].
    split.
    + intros weight Hin.
      assert (In weight (sublist 0 active scratch)) as Hin_old.
      {
        eapply Permutation_in.
        - apply Permutation_sym. exact Hremove.
        - exact Hin.
      }
      destruct
        (in_sublist0_has_index__removals_bounds
          Z scratch 0 weight active)
        as [k [Hk Hnth]]; [lia|exact Hin_old|].
      rewrite <- Hnth.
      apply Hscan. exact Hk.
    + exact Hresidual.
Qed.
Lemma sum_permutation__removals_bounds :
  forall left right : list Z,
    Permutation left right -> sum left = sum right.
Proof.
  intros left right Hperm.
  induction Hperm; simpl; lia.
Qed.
Lemma sum_nonnegative_forall__removals_bounds :
  forall l,
    Forall (fun z => 0 <= z) l ->
    0 <= sum l.
Proof.
  intros l Hnonneg.
  induction Hnonneg; simpl; lia.
Qed.
Lemma sum_contains_nonnegative__removals_bounds :
  forall (l : list Z) value,
    Forall (fun z => 0 <= z) l ->
    In value l ->
    value <= sum l.
Proof.
  intros l value Hnonneg Hin.
  induction Hnonneg as [|head tail Hhead Htail IH].
  - contradiction.
  - simpl in Hin. simpl.
    destruct Hin as [Heq | Hin].
    + subst.
      pose proof (sum_nonnegative_forall__removals_bounds tail Htail).
      lia.
    + specialize (IH Hin). lia.
Qed.
Lemma huffman_input_sum_bound__removals_bounds :
  forall input n,
    Zlength input = n ->
    1 <= n <= 8 ->
    HuffmanInputBounded input ->
    0 <= sum input <= 8000.
Proof.
  intros input n Hlength Hn Hbounded.
  pose proof (sum_bound 1000 input) as Hsum.
  assert (forall i, 0 <= i -> 0 <= Znth i input 0 <= 1000) as Hall.
  {
    intros i Hi.
    destruct (Z_lt_ge_dec i (Zlength input)) as [Hin | Hout].
    - specialize (Hbounded i). lia.
    - unfold Znth. rewrite nth_overflow.
      + lia.
      + rewrite Zlength_correct in Hout. lia.
  }
  specialize (Hsum Hall).
  rewrite <- Zlength_correct, Hlength in Hsum.
  lia.
Qed.
Lemma huffman_bounded_competitor__removals_bounds :
  forall l,
    l <> [] ->
    Forall (fun z => 0 <= z) l ->
    exists tree,
      HuffmanLeaves tree = l /\
      HuffmanWeightedPathLength tree <=
        Z.of_nat (length l - 1) * sum l.
Proof.
  intros l Hnonempty Hnonneg.
  induction l as [|head tail IH]; [contradiction|].
  destruct tail as [|next rest].
  - exists (HuffmanLeaf head). simpl. split; [reflexivity|lia].
  - inversion Hnonneg as [|? ? Hhead Htail]; subst.
    specialize (IH ltac:(discriminate) Htail).
    destruct IH as [tree [Hleaves Hcost]].
    exists (HuffmanNode (HuffmanLeaf head) tree).
    split.
    + simpl. rewrite Hleaves. reflexivity.
    + simpl.
      rewrite huffman_tree_weight_leaves, Hleaves.
      pose proof (sum_nonnegative_forall__removals_bounds _ Htail) as Hsum.
      simpl in Hcost |- *.
      rewrite Nat.sub_0_r in Hcost.
      assert (0 <= Z.of_nat (length rest) * head) by
        (apply Z.mul_nonneg_nonneg; lia).
      change
        (HuffmanWeightedPathLength tree + head + (next + sum rest) <=
         Z.of_nat (S (length rest)) *
           (head + (next + sum rest))).
      rewrite Nat2Z.inj_succ.
      unfold Z.succ.
      rewrite Z.mul_add_distr_l.
      repeat rewrite Z.mul_add_distr_r.
      rewrite !Z.mul_1_l.
      lia.
Qed.
Lemma huffman_optimal_input_upper__removals_bounds :
  forall input n optimum,
    Zlength input = n ->
    1 <= n <= 8 ->
    HuffmanInputBounded input ->
    HuffmanOptimalCost input optimum ->
    optimum <= 56000.
Proof.
  intros input n optimum Hlength Hn Hbounded Hoptimum.
  destruct input as [|head tail].
  - rewrite Zlength_correct in Hlength. simpl in Hlength. lia.
  - assert (0 <= head /\ Forall (fun z => 0 <= z) tail) as Hnonneg.
    {
      split.
      - specialize (Hbounded 0).
        assert (0 <= 0 < Zlength (head :: tail)) by
          (rewrite Zlength_correct; simpl; lia).
        specialize (Hbounded H).
        unfold Znth in Hbounded. simpl in Hbounded. lia.
      - rewrite Forall_forall.
        intros value Hin.
        destruct (In_nth tail value 0 Hin) as [k [Hk Hvalue]].
        specialize (Hbounded (Z.of_nat (S k))).
        simpl in Hlength.
        assert (0 <= Z.of_nat (S k) < Zlength (head :: tail)) by
          (rewrite Zlength_correct; simpl; lia).
        specialize (Hbounded H).
        unfold Znth in Hbounded.
        rewrite Nat2Z.id in Hbounded.
        simpl in Hbounded.
        rewrite Hvalue in Hbounded. lia.
    }
  destruct Hnonneg as [Hhead Htail].
  destruct Hoptimum as [best [[Hbest_feasible Hbest_le] Hbest_cost]].
  destruct
    (huffman_bounded_competitor__removals_bounds
      (head :: tail) ltac:(discriminate) (Forall_cons _ Hhead Htail))
    as [competitor [Hcompetitor_leaves Hcompetitor_bound]].
  assert
    (HuffmanTreeFeasible (head :: tail) competitor) as Hcompetitor_feasible.
  {
    unfold HuffmanTreeFeasible.
    rewrite Hcompetitor_leaves.
    apply Permutation_refl.
  }
  specialize (Hbest_le _ Hcompetitor_feasible).
  pose proof
    (huffman_input_sum_bound__removals_bounds
      (head :: tail) n Hlength Hn Hbounded)
    as Hsum_bound.
  rewrite <- Hbest_cost.
  eapply Z.le_trans; [exact Hbest_le|].
  rewrite Zlength_correct in Hlength.
  change (Z.of_nat (S (length tail)) = n) in Hlength.
  rewrite Nat2Z.inj_succ in Hlength.
  unfold Z.succ in Hlength.
  simpl in Hcompetitor_bound.
  simpl in Hsum_bound.
  rewrite Nat.sub_0_r in Hcompetitor_bound.
  eapply Z.le_trans; [exact Hcompetitor_bound|].
  eapply Z.le_trans with (m := 7 * (head + sum tail)).
  + apply Z.mul_le_mono_nonneg_r.
    * lia.
    * lia.
  + eapply Z.le_trans with (m := 7 * 8000).
    * apply Z.mul_le_mono_nonneg_l; lia.
    * lia.
Qed.
Lemma huffman_tree_cost_nonnegative__removals_bounds :
  forall tree,
    Forall (fun z => 0 <= z) (HuffmanLeaves tree) ->
    0 <= HuffmanWeightedPathLength tree.
Proof.
  intros tree.
  induction tree as [weight|left IHleft right IHright]; intros Hnonneg.
  - simpl. lia.
  - simpl in Hnonneg |- *.
    rewrite Forall_app in Hnonneg.
    destruct Hnonneg as [Hleft Hright].
    pose proof (IHleft Hleft).
    pose proof (IHright Hright).
    assert (0 <= HuffmanTreeWeight left).
    {
      rewrite huffman_tree_weight_leaves.
      apply sum_nonnegative_forall__removals_bounds.
      exact Hleft.
    }
    assert (0 <= HuffmanTreeWeight right).
    {
      rewrite huffman_tree_weight_leaves.
      apply sum_nonnegative_forall__removals_bounds.
      exact Hright.
    }
    lia.
Qed.
Lemma huffman_nontrivial_cost_ge_weight__removals_bounds :
  forall tree,
    2 <= Zlength (HuffmanLeaves tree) ->
    Forall (fun z => 0 <= z) (HuffmanLeaves tree) ->
    HuffmanTreeWeight tree <= HuffmanWeightedPathLength tree.
Proof.
  intros tree Hlength Hnonneg.
  destruct tree as [weight|left right].
  - rewrite Zlength_correct in Hlength. simpl in Hlength. lia.
  - simpl in Hnonneg |- *.
    rewrite Forall_app in Hnonneg.
    destruct Hnonneg as [Hleft Hright].
    pose proof (huffman_tree_cost_nonnegative__removals_bounds left Hleft).
    pose proof (huffman_tree_cost_nonnegative__removals_bounds right Hright).
    lia.
Qed.
Lemma huffman_optimal_cost_ge_sum__removals_bounds :
  forall live optimum,
    2 <= Zlength live ->
    Forall (fun z => 0 <= z) live ->
    HuffmanOptimalCost live optimum ->
    sum live <= optimum.
Proof.
  intros live optimum Hlength Hnonneg Hoptimum.
  destruct Hoptimum as [best [[Hfeasible _] Hcost]].
  unfold HuffmanTreeFeasible in Hfeasible.
  assert (2 <= Zlength (HuffmanLeaves best)) as Hleaves_length.
  {
    pose proof (Permutation_length Hfeasible) as Hperm_length.
    rewrite Zlength_correct in Hlength |- *.
    lia.
  }
  assert (Forall (fun z => 0 <= z) (HuffmanLeaves best)) as Hleaves_nonneg.
  {
    rewrite Forall_forall in Hnonneg |- *.
    intros value Hin.
    apply Hnonneg.
    eapply Permutation_in; [apply Permutation_sym; exact Hfeasible|exact Hin].
  }
  pose proof
    (huffman_nontrivial_cost_ge_weight__removals_bounds
      best Hleaves_length Hleaves_nonneg) as Hcost_ge.
  rewrite huffman_tree_weight_leaves in Hcost_ge.
  pose proof (sum_permutation__removals_bounds _ _ Hfeasible) as Hsum.
  lia.
Qed.
Lemma huffman_residual_charge_bounds__removals_bounds :
  forall input scratch active held selected accumulated n,
    Zlength input = n ->
    Zlength scratch = n ->
    1 <= n <= 8 ->
    HuffmanInputBounded input ->
    1 <= active < n ->
    0 <= selected < active ->
    1 <= held ->
    HuffmanFirstHeldLegacy input scratch active held accumulated ->
    held + Znth selected scratch 0 <= 8000 /\
    accumulated + held + Znth selected scratch 0 <= 56000.
Proof.
  intros input scratch active held selected accumulated n
    Hinput_length Hscratch_length Hn Hbounded Hactive Hselected Hheld Hfirst.
  destruct Hfirst as
    [prior_live [Hprior [Hheld_le [Hsum [remaining [Hopt_live Hopt_input]]]]]].
  assert (Forall (fun z => 0 <= z) prior_live) as Hprior_nonneg.
  {
    rewrite Forall_forall.
    intros value Hin.
    specialize (Hheld_le value Hin). lia.
  }
  assert (In (Znth selected scratch 0) (sublist 0 active scratch)) as Hselected_in.
  {
    rewrite <- (Znth_sublist0 0 selected active scratch) by lia.
    apply nth_In.
    pose proof (Zlength_sublist0 active scratch ltac:(lia)) as Hlive_length.
    rewrite Zlength_correct in Hlive_length.
    lia.
  }
  assert (Forall (fun z => 0 <= z) (sublist 0 active scratch)) as Hlive_nonneg.
  {
    rewrite Forall_forall in Hprior_nonneg |- *.
    intros value Hin.
    apply Hprior_nonneg.
    eapply Permutation_in; [apply Permutation_sym; exact Hprior|].
    simpl. auto.
  }
  pose proof
    (sum_contains_nonnegative__removals_bounds
      (sublist 0 active scratch) (Znth selected scratch 0)
      Hlive_nonneg Hselected_in) as Hselected_sum.
  pose proof (sum_permutation__removals_bounds _ _ Hprior) as Hprior_sum.
  pose proof
    (huffman_input_sum_bound__removals_bounds input n
      Hinput_length Hn Hbounded) as Hinput_bound.
  assert (2 <= Zlength prior_live) as Hprior_length.
  {
    pose proof (Permutation_length Hprior) as Hperm_length.
    pose proof (Zlength_sublist0 active scratch ltac:(lia)) as Hsub.
    rewrite Zlength_correct in Hsub.
    rewrite Zlength_correct.
    rewrite Hperm_length.
    change
      (2 <= Z.of_nat (S (length (sublist 0 active scratch)))).
    rewrite Nat2Z.inj_succ.
    unfold Z.succ.
    lia.
  }
  pose proof
    (huffman_optimal_cost_ge_sum__removals_bounds
      prior_live remaining Hprior_length Hprior_nonneg Hopt_live)
    as Hremaining_lower.
  pose proof
    (huffman_optimal_input_upper__removals_bounds
      input n (accumulated + remaining)
      Hinput_length Hn Hbounded Hopt_input)
    as Htotal_upper.
  simpl in Hprior_sum.
  split; lia.
Qed.
Lemma huffman_optimal_cost_permutation__merge_transition :
  forall left right answer,
    Permutation left right ->
    HuffmanOptimalCost left answer ->
    HuffmanOptimalCost right answer.
Proof.
  intros left right answer Hperm Hoptimal.
  unfold HuffmanOptimalCost, min_value_of_subset,
    min_object_of_subset in *.
  destruct Hoptimal as [best [[Hbest Hminimal] Hcost]].
  exists best.
  split; [split|]; [| |exact Hcost].
  - unfold HuffmanTreeFeasible in *.
    eapply Permutation_trans.
    + apply Permutation_sym. exact Hperm.
    + exact Hbest.
  - intros candidate Hcandidate.
    apply Hminimal.
    unfold HuffmanTreeFeasible in *.
    eapply Permutation_trans; [exact Hperm|exact Hcandidate].
Qed.
Lemma permutation_swap_across_middle__merge_transition :
  forall (A : Type) (first last : A) middle suffix,
    Permutation
      (first :: middle ++ last :: suffix)
      (last :: middle ++ first :: suffix).
Proof.
  intros A first last middle suffix.
  eapply Permutation_trans.
  - apply perm_skip.
    apply Permutation_sym.
    apply Permutation_middle.
  - eapply Permutation_trans.
    + apply perm_swap.
    + apply perm_skip.
      apply Permutation_middle.
Qed.
Lemma huffman_weighted_swap_to_front__merge_transition :
  forall first last middle suffix maximum middle_depths last_depth suffix_depths,
    length middle = length middle_depths ->
    last <= first ->
    last_depth <= maximum ->
    HuffmanWeightedDepths
      (last :: middle ++ first :: suffix)
      (maximum :: middle_depths ++ last_depth :: suffix_depths) <=
    HuffmanWeightedDepths
      (first :: middle ++ last :: suffix)
      (maximum :: middle_depths ++ last_depth :: suffix_depths).
Proof.
  unfold HuffmanWeightedDepths.
  intros first last middle.
  induction middle as [|middle_head middle IH];
    intros suffix maximum middle_depths last_depth suffix_depths
      Hlength Hweight Hdepth.
  - destruct middle_depths; [simpl; nia|discriminate].
  - destruct middle_depths as [|depth_head middle_depths]; [discriminate|].
    simpl in Hlength |- *.
    apply Nat.succ_inj in Hlength.
    specialize
      (IH suffix maximum middle_depths last_depth suffix_depths
        Hlength Hweight Hdepth).
    simpl in IH.
    nia.
Qed.
Lemma huffman_two_minima_to_maximum_slots__merge_transition :
  forall x y rest weights depths maximum,
    Permutation (x :: y :: rest) weights ->
    (forall weight, In weight (x :: y :: rest) -> x <= weight) ->
    (forall weight, In weight (y :: rest) -> y <= weight) ->
    depths <> [] ->
    length weights = length depths ->
    (exists depth_tail, depths = maximum :: maximum :: depth_tail) ->
    Forall (fun depth => depth <= maximum) depths ->
    exists reordered_rest,
      Permutation rest reordered_rest /\
      HuffmanWeightedDepths (x :: y :: reordered_rest) depths <=
      HuffmanWeightedDepths weights depths.
Proof.
  unfold HuffmanWeightedDepths.
  intros x y rest weights depths maximum Hperm Hxmin Hymin
    Hdepth_nonempty Hlength [depth_tail Hdepths] Hdepth_bound.
  subst depths.
  assert (Hin_x : In x weights).
  {
    eapply Permutation_in; [exact Hperm|].
    simpl; auto.
  }
  destruct (in_split x weights Hin_x) as [before_x [after_x Hweights]].
  destruct before_x as [|head_x middle_x].
  - simpl in Hweights. subst weights.
    assert (Htail_perm : Permutation (y :: rest) after_x).
    {
      apply Permutation_cons_inv with x.
      exact Hperm.
    }
    assert (Hin_y : In y after_x).
    {
      eapply Permutation_in; [exact Htail_perm|].
      simpl; auto.
    }
    destruct (in_split y after_x) as [before_y [after_y Hafter_x]];
      [exact Hin_y|].
    destruct before_y as [|head_y middle_y].
    + simpl in Hafter_x. subst after_x.
      exists after_y.
      split.
      * apply Permutation_cons_inv with y. exact Htail_perm.
      * lia.
    + assert (Hlen_mid_y :
        (length middle_y < length depth_tail)%nat).
      {
        simpl in Hlength.
        rewrite Hafter_x in Hlength.
        rewrite length_app in Hlength.
        simpl in Hlength.
        lia.
      }
      pose (depth_middle_y := firstn (length middle_y) depth_tail).
      pose (depth_y := nth (length middle_y) depth_tail 0).
      pose (depth_after_y := skipn (S (length middle_y)) depth_tail).
      assert (Hdepth_tail_shape :
        depth_tail = depth_middle_y ++ depth_y :: depth_after_y).
      {
        unfold depth_middle_y, depth_y, depth_after_y.
        symmetry.
        apply firstn_skipn_middle.
        apply nth_error_nth'.
        exact Hlen_mid_y.
      }
      assert (Hdepth_y_le : depth_y <= maximum).
      {
        rewrite Forall_forall in Hdepth_bound.
        apply Hdepth_bound.
        simpl. right. right.
        unfold depth_y. apply nth_In. exact Hlen_mid_y.
      }
      assert (Hy_head : y <= head_y).
      {
        apply Hymin.
        eapply Permutation_in.
        - apply Permutation_sym. exact Htail_perm.
        - rewrite Hafter_x. simpl; auto.
      }
      exists (middle_y ++ head_y :: after_y).
      split.
      * apply Permutation_cons_inv with y.
        eapply Permutation_trans; [exact Htail_perm|].
        rewrite Hafter_x.
        apply permutation_swap_across_middle__merge_transition.
      * rewrite Hafter_x, Hdepth_tail_shape.
        simpl.
        apply Z.add_le_mono_l.
        apply huffman_weighted_swap_to_front__merge_transition.
        -- unfold depth_middle_y. rewrite length_firstn.
           rewrite Nat.min_l by (simpl; lia). reflexivity.
        -- exact Hy_head.
        -- exact Hdepth_y_le.
  - assert (Hlen_mid_x :
      (length middle_x < S (length depth_tail))%nat).
    {
      rewrite Hweights in Hlength.
      rewrite length_app in Hlength.
      simpl in Hlength.
      lia.
    }
    pose (depth_middle_x := firstn (length middle_x) (maximum :: depth_tail)).
    pose (depth_x := nth (length middle_x) (maximum :: depth_tail) 0).
    pose (depth_after_x :=
      skipn (S (length middle_x)) (maximum :: depth_tail)).
    assert (Hdepth_after_head_shape :
      maximum :: depth_tail =
        depth_middle_x ++ depth_x :: depth_after_x).
    {
      unfold depth_middle_x, depth_x, depth_after_x.
      symmetry.
      apply firstn_skipn_middle.
      apply nth_error_nth'. exact Hlen_mid_x.
    }
    assert (Hdepth_x_le : depth_x <= maximum).
    {
      rewrite Forall_forall in Hdepth_bound.
      apply Hdepth_bound.
      right.
      unfold depth_x. apply nth_In. exact Hlen_mid_x.
    }
    assert (Hx_head : x <= head_x).
    {
      apply Hxmin.
      eapply Permutation_in.
      - apply Permutation_sym. exact Hperm.
      - rewrite Hweights. simpl; auto.
    }
    pose (tail_after_x := middle_x ++ head_x :: after_x).
    assert (Hpromoted_perm :
      Permutation weights (x :: tail_after_x)).
    {
      rewrite Hweights.
      unfold tail_after_x.
      apply permutation_swap_across_middle__merge_transition.
    }
    assert (Htail_perm : Permutation (y :: rest) tail_after_x).
    {
      apply Permutation_cons_inv with x.
      eapply Permutation_trans; [exact Hperm|exact Hpromoted_perm].
    }
    assert (Hfirst_cost :
      HuffmanWeightedDepths
        (x :: tail_after_x) (maximum :: maximum :: depth_tail) <=
      HuffmanWeightedDepths
        weights (maximum :: maximum :: depth_tail)).
    {
      unfold HuffmanWeightedDepths.
      rewrite Hweights, Hdepth_after_head_shape.
      unfold tail_after_x.
      apply huffman_weighted_swap_to_front__merge_transition.
      - unfold depth_middle_x. rewrite length_firstn.
        rewrite Nat.min_l by (simpl; lia). reflexivity.
      - exact Hx_head.
      - exact Hdepth_x_le.
    }
    assert (Hin_y : In y tail_after_x).
    {
      eapply Permutation_in; [exact Htail_perm|]. simpl; auto.
    }
    destruct (in_split y tail_after_x) as [before_y [after_y Htail_shape]];
      [exact Hin_y|].
    destruct before_y as [|head_y middle_y].
    + simpl in Htail_shape. subst tail_after_x.
      exists after_y.
      split.
      * apply Permutation_cons_inv with y.
        rewrite <- Htail_shape. exact Htail_perm.
      * rewrite <- Htail_shape. exact Hfirst_cost.
    + assert (Hlen_tail :
        length tail_after_x = S (length depth_tail)).
      {
        pose proof (Permutation_length Hpromoted_perm) as Hp_len.
        rewrite Hlength in Hp_len. simpl in Hp_len. lia.
      }
      assert (Hlen_mid_y :
        (length middle_y < length depth_tail)%nat).
      {
        rewrite Htail_shape in Hlen_tail.
        rewrite length_app in Hlen_tail.
        simpl in Hlen_tail. lia.
      }
      pose (depth_middle_y := firstn (length middle_y) depth_tail).
      pose (depth_y := nth (length middle_y) depth_tail 0).
      pose (depth_after_y := skipn (S (length middle_y)) depth_tail).
      assert (Hdepth_tail_shape :
        depth_tail = depth_middle_y ++ depth_y :: depth_after_y).
      {
        unfold depth_middle_y, depth_y, depth_after_y.
        symmetry.
        apply firstn_skipn_middle.
        apply nth_error_nth'. exact Hlen_mid_y.
      }
      assert (Hdepth_y_le : depth_y <= maximum).
      {
        rewrite Forall_forall in Hdepth_bound.
        apply Hdepth_bound.
        simpl. right. right.
        unfold depth_y. apply nth_In. exact Hlen_mid_y.
      }
      assert (Hy_head : y <= head_y).
      {
        apply Hymin.
        eapply Permutation_in.
        - apply Permutation_sym. exact Htail_perm.
        - rewrite Htail_shape. simpl; auto.
      }
      exists (middle_y ++ head_y :: after_y).
      split.
      * apply Permutation_cons_inv with y.
        eapply Permutation_trans; [exact Htail_perm|].
        rewrite Htail_shape.
        apply permutation_swap_across_middle__merge_transition.
      * eapply Z.le_trans; [|exact Hfirst_cost].
        unfold HuffmanWeightedDepths in *.
        rewrite Htail_shape, Hdepth_tail_shape.
        simpl.
        apply Z.add_le_mono_l.
        apply huffman_weighted_swap_to_front__merge_transition.
        -- unfold depth_middle_y. rewrite length_firstn.
           rewrite Nat.min_l by (simpl; lia). reflexivity.
        -- exact Hy_head.
        -- exact Hdepth_y_le.
Qed.
Lemma huffman_relabel_profile__merge_transition :
  forall tree weights,
    length weights = length (HuffmanLeaves tree) ->
    exists relabeled,
      HuffmanLeaves relabeled = weights /\
      HuffmanTreeWeight relabeled = sum weights /\
      HuffmanWeightedDepths weights (HuffmanLeafDepths tree) =
        HuffmanWeightedPathLength relabeled.
Proof.
  intros tree.
  induction tree as [old_weight|left IHleft right IHright];
    intros weights Hlength.
  - destruct weights as [|weight tail]; [discriminate|].
    destruct tail; [|discriminate].
    exists (HuffmanLeaf weight).
    unfold HuffmanWeightedDepths. simpl. repeat split; lia.
  - pose (left_weights := firstn (length (HuffmanLeaves left)) weights).
    pose (right_weights := skipn (length (HuffmanLeaves left)) weights).
    assert (Hleft_length :
      length left_weights = length (HuffmanLeaves left)).
    {
      unfold left_weights.
      rewrite length_firstn, Nat.min_l; [reflexivity|].
      simpl in Hlength. rewrite length_app in Hlength. lia.
    }
    assert (Hright_length :
      length right_weights = length (HuffmanLeaves right)).
    {
      unfold right_weights.
      rewrite length_skipn.
      simpl in Hlength. rewrite length_app in Hlength. lia.
    }
    destruct (IHleft left_weights Hleft_length) as
      [new_left [Hleft_leaves [Hleft_weight Hleft_cost]]].
    destruct (IHright right_weights Hright_length) as
      [new_right [Hright_leaves [Hright_weight Hright_cost]]].
    exists (HuffmanNode new_left new_right).
    split.
    + simpl. rewrite Hleft_leaves, Hright_leaves.
      unfold left_weights, right_weights.
      apply firstn_skipn.
    + split.
      * simpl. rewrite Hleft_weight, Hright_weight.
        rewrite <- sum_app.
        unfold left_weights, right_weights.
        rewrite firstn_skipn. reflexivity.
      * replace weights with (left_weights ++ right_weights).
        2:{ unfold left_weights, right_weights. apply firstn_skipn. }
        simpl HuffmanLeafDepths.
        rewrite huffman_weighted_depths_app.
        2:{ rewrite length_map, Hleft_length.
            apply (proj1 (huffman_leaf_depth_profile left)). }
        rewrite huffman_weighted_depths_lift.
        2:{ rewrite Hleft_length.
            apply (proj1 (huffman_leaf_depth_profile left)). }
        rewrite huffman_weighted_depths_lift.
        2:{ rewrite Hright_length.
            apply (proj1 (huffman_leaf_depth_profile right)). }
        rewrite Hleft_cost, Hright_cost.
        simpl.
        rewrite Hleft_weight, Hright_weight.
        lia.
Qed.
Lemma huffman_normalized_pair_profile__merge_transition :
  forall context old_first old_second,
    exists normalized depth_tail,
      Permutation
        (HuffmanLeaves normalized)
        (HuffmanLeaves
          (HuffmanPlug context
            (HuffmanNode
              (HuffmanLeaf old_first) (HuffmanLeaf old_second)))) /\
      HuffmanTreeWeight normalized =
        HuffmanTreeWeight
          (HuffmanPlug context
            (HuffmanNode
              (HuffmanLeaf old_first) (HuffmanLeaf old_second))) /\
      HuffmanWeightedPathLength normalized =
        HuffmanWeightedPathLength
          (HuffmanPlug context
            (HuffmanNode
              (HuffmanLeaf old_first) (HuffmanLeaf old_second))) /\
      HuffmanTreeHeight normalized =
        HuffmanTreeHeight
          (HuffmanPlug context
            (HuffmanNode
              (HuffmanLeaf old_first) (HuffmanLeaf old_second))) /\
      HuffmanLeafDepths normalized =
        (HuffmanContextDepth context + 1) ::
          (HuffmanContextDepth context + 1) :: depth_tail /\
      (forall weights,
        length weights = length (HuffmanLeaves normalized) ->
        exists relabeled,
          HuffmanLeaves relabeled = weights /\
          HuffmanTreeWeight relabeled = sum weights /\
          HuffmanWeightedDepths weights (HuffmanLeafDepths normalized) =
            HuffmanWeightedPathLength relabeled /\
          (forall first second rest,
            weights = first :: second :: rest ->
            exists contracted,
              HuffmanLeaves contracted = (first + second) :: rest /\
              HuffmanTreeWeight relabeled = HuffmanTreeWeight contracted /\
              HuffmanWeightedPathLength relabeled =
                HuffmanWeightedPathLength contracted + first + second)).
Proof.
  intros context.
  induction context as
      [|inner IH sibling|sibling inner IH]; intros old_first old_second.
  - exists
      (HuffmanNode
        (HuffmanLeaf old_first) (HuffmanLeaf old_second)), [].
    repeat split; try reflexivity.
    intros weights Hlength.
    destruct weights as [|first [|second tail]]; try discriminate.
    destruct tail; [|discriminate].
    exists (HuffmanNode (HuffmanLeaf first) (HuffmanLeaf second)).
    unfold HuffmanWeightedDepths. simpl.
    repeat split; try lia.
    intros x y rest Heq.
    inversion Heq; subst.
    exists (HuffmanLeaf (x + y)).
    simpl. repeat split; lia.
  - destruct (IH old_first old_second) as
      [normalized_inner [inner_depth_tail
        [Hinner_leaves [Hinner_weight [Hinner_cost
          [Hinner_height [Hinner_depths Hinner_relabel]]]]]]].
    exists (HuffmanNode normalized_inner sibling),
      (map (fun depth => depth + 1) inner_depth_tail ++
        map (fun depth => depth + 1) (HuffmanLeafDepths sibling)).
    split.
    + simpl. apply Permutation_app; [exact Hinner_leaves|reflexivity].
    + split.
      * simpl. rewrite Hinner_weight. reflexivity.
      * split.
        -- simpl. rewrite Hinner_cost, Hinner_weight. reflexivity.
        -- split.
           ++ simpl. rewrite Hinner_height. reflexivity.
           ++ split.
              ** simpl HuffmanLeafDepths. rewrite Hinner_depths. simpl.
                 reflexivity.
              ** intros weights Hweights_length.
                 pose (left_weights :=
                   firstn (length (HuffmanLeaves normalized_inner)) weights).
                 pose (right_weights :=
                   skipn (length (HuffmanLeaves normalized_inner)) weights).
                 assert (Hleft_length :
                   length left_weights =
                     length (HuffmanLeaves normalized_inner)).
                 {
                   unfold left_weights.
                   rewrite length_firstn, Nat.min_l; [reflexivity|].
                   simpl in Hweights_length.
                   rewrite length_app in Hweights_length. lia.
                 }
                 assert (Hright_length :
                   length right_weights = length (HuffmanLeaves sibling)).
                 {
                   unfold right_weights. rewrite length_skipn.
                   simpl in Hweights_length.
                   rewrite length_app in Hweights_length. lia.
                 }
                 destruct (Hinner_relabel left_weights Hleft_length) as
                   [new_inner [Hnew_inner_leaves [Hnew_inner_weight
                     [Hnew_inner_cost Hnew_inner_contract]]]].
                 destruct (huffman_relabel_profile__merge_transition
                   sibling right_weights Hright_length) as
                   [new_sibling [Hnew_sibling_leaves
                     [Hnew_sibling_weight Hnew_sibling_cost]]].
                 exists (HuffmanNode new_inner new_sibling).
                 split.
                 { simpl. rewrite Hnew_inner_leaves, Hnew_sibling_leaves.
                   unfold left_weights, right_weights.
                   apply firstn_skipn. }
                 split.
                 { simpl. rewrite Hnew_inner_weight, Hnew_sibling_weight.
                   rewrite <- sum_app.
                   unfold left_weights, right_weights.
                   rewrite firstn_skipn. reflexivity. }
                 split.
                 { replace weights with (left_weights ++ right_weights).
                   2:{ unfold left_weights, right_weights.
                       apply firstn_skipn. }
                   simpl HuffmanLeafDepths.
                   rewrite huffman_weighted_depths_app.
                   2:{ rewrite length_map, Hleft_length.
                       apply (proj1
                         (huffman_leaf_depth_profile normalized_inner)). }
                   rewrite huffman_weighted_depths_lift.
                   2:{ rewrite Hleft_length.
                       apply (proj1
                         (huffman_leaf_depth_profile normalized_inner)). }
                   rewrite huffman_weighted_depths_lift.
                   2:{ rewrite Hright_length.
                       apply (proj1 (huffman_leaf_depth_profile sibling)). }
                   rewrite Hnew_inner_cost, Hnew_sibling_cost.
                   simpl. rewrite Hnew_inner_weight, Hnew_sibling_weight.
                   lia. }
                 intros first second rest Hweights.
                 pose proof
                   (proj1 (huffman_leaf_depth_profile normalized_inner))
                   as Hinner_profile_length.
                 rewrite Hinner_depths in Hinner_profile_length.
                 assert (Hinner_two :
                   (2 <= length (HuffmanLeaves normalized_inner))%nat)
                   by (simpl in Hinner_profile_length; lia).
                 remember (length (HuffmanLeaves normalized_inner))
                   as inner_length eqn:Hinner_length.
                 destruct inner_length as [|[|inner_rest_length]]; try lia.
                 subst weights.
                 assert (Hleft_shape :
                   left_weights = first :: second ::
                     firstn inner_rest_length rest).
                 {
                   unfold left_weights.
                   reflexivity.
                 }
                 destruct (Hnew_inner_contract first second
                   (firstn inner_rest_length rest) Hleft_shape) as
                   [contracted_inner [Hcontracted_leaves
                     [Hcontracted_weight Hcontracted_cost]]].
                 exists (HuffmanNode contracted_inner new_sibling).
                 split.
                 { simpl. rewrite Hcontracted_leaves, Hnew_sibling_leaves.
                   unfold right_weights.
                   simpl.
                   rewrite firstn_skipn. reflexivity. }
                 split.
                 { simpl. rewrite Hcontracted_weight. reflexivity. }
                 simpl. rewrite Hcontracted_cost, Hcontracted_weight. lia.
  - destruct (IH old_first old_second) as
      [normalized_inner [inner_depth_tail
        [Hinner_leaves [Hinner_weight [Hinner_cost
          [Hinner_height [Hinner_depths Hinner_relabel]]]]]]].
    exists (HuffmanNode normalized_inner sibling),
      (map (fun depth => depth + 1) inner_depth_tail ++
        map (fun depth => depth + 1) (HuffmanLeafDepths sibling)).
    split.
    + simpl.
      eapply Permutation_trans.
      * apply Permutation_app; [exact Hinner_leaves|reflexivity].
      * apply Permutation_app_comm.
    + split.
      * simpl. rewrite Hinner_weight. lia.
      * split.
        -- simpl. rewrite Hinner_cost, Hinner_weight. lia.
        -- split.
           ++ simpl. rewrite Hinner_height, Z.max_comm. reflexivity.
           ++ split.
              ** simpl HuffmanLeafDepths. rewrite Hinner_depths. simpl.
                 reflexivity.
              ** intros weights Hweights_length.
                 pose (left_weights :=
                   firstn (length (HuffmanLeaves normalized_inner)) weights).
                 pose (right_weights :=
                   skipn (length (HuffmanLeaves normalized_inner)) weights).
                 assert (Hleft_length :
                   length left_weights =
                     length (HuffmanLeaves normalized_inner)).
                 {
                   unfold left_weights.
                   rewrite length_firstn, Nat.min_l; [reflexivity|].
                   simpl in Hweights_length.
                   rewrite length_app in Hweights_length. lia.
                 }
                 assert (Hright_length :
                   length right_weights = length (HuffmanLeaves sibling)).
                 {
                   unfold right_weights. rewrite length_skipn.
                   simpl in Hweights_length.
                   rewrite length_app in Hweights_length. lia.
                 }
                 destruct (Hinner_relabel left_weights Hleft_length) as
                   [new_inner [Hnew_inner_leaves [Hnew_inner_weight
                     [Hnew_inner_cost Hnew_inner_contract]]]].
                 destruct (huffman_relabel_profile__merge_transition
                   sibling right_weights Hright_length) as
                   [new_sibling [Hnew_sibling_leaves
                     [Hnew_sibling_weight Hnew_sibling_cost]]].
                 exists (HuffmanNode new_inner new_sibling).
                 split.
                 { simpl. rewrite Hnew_inner_leaves, Hnew_sibling_leaves.
                   unfold left_weights, right_weights.
                   apply firstn_skipn. }
                 split.
                 { simpl. rewrite Hnew_inner_weight, Hnew_sibling_weight.
                   rewrite <- sum_app.
                   unfold left_weights, right_weights.
                   rewrite firstn_skipn. reflexivity. }
                 split.
                 { replace weights with (left_weights ++ right_weights).
                   2:{ unfold left_weights, right_weights.
                       apply firstn_skipn. }
                   simpl HuffmanLeafDepths.
                   rewrite huffman_weighted_depths_app.
                   2:{ rewrite length_map, Hleft_length.
                       apply (proj1
                         (huffman_leaf_depth_profile normalized_inner)). }
                   rewrite huffman_weighted_depths_lift.
                   2:{ rewrite Hleft_length.
                       apply (proj1
                         (huffman_leaf_depth_profile normalized_inner)). }
                   rewrite huffman_weighted_depths_lift.
                   2:{ rewrite Hright_length.
                       apply (proj1 (huffman_leaf_depth_profile sibling)). }
                   rewrite Hnew_inner_cost, Hnew_sibling_cost.
                   simpl. rewrite Hnew_inner_weight, Hnew_sibling_weight.
                   lia. }
                 intros first second rest Hweights.
                 pose proof
                   (proj1 (huffman_leaf_depth_profile normalized_inner))
                   as Hinner_profile_length.
                 rewrite Hinner_depths in Hinner_profile_length.
                 assert (Hinner_two :
                   (2 <= length (HuffmanLeaves normalized_inner))%nat)
                   by (simpl in Hinner_profile_length; lia).
                 remember (length (HuffmanLeaves normalized_inner))
                   as inner_length eqn:Hinner_length.
                 destruct inner_length as [|[|inner_rest_length]]; try lia.
                 subst weights.
                 assert (Hleft_shape :
                   left_weights = first :: second ::
                     firstn inner_rest_length rest).
                 {
                   unfold left_weights.
                   reflexivity.
                 }
                 destruct (Hnew_inner_contract first second
                   (firstn inner_rest_length rest) Hleft_shape) as
                   [contracted_inner [Hcontracted_leaves
                     [Hcontracted_weight Hcontracted_cost]]].
                 exists (HuffmanNode contracted_inner new_sibling).
                 split.
                 { simpl. rewrite Hcontracted_leaves, Hnew_sibling_leaves.
                   unfold right_weights.
                   simpl.
                   rewrite firstn_skipn. reflexivity. }
                 split.
                 { simpl. rewrite Hcontracted_weight. reflexivity. }
                 simpl. rewrite Hcontracted_cost, Hcontracted_weight. lia.
Qed.
Lemma huffman_expand_contracted_tree__merge_transition :
  forall x y rest contracted,
    Permutation (rest ++ [x + y]) (HuffmanLeaves contracted) ->
    exists expanded,
      Permutation (x :: y :: rest) (HuffmanLeaves expanded) /\
      HuffmanTreeWeight expanded = HuffmanTreeWeight contracted /\
      HuffmanWeightedPathLength expanded =
        HuffmanWeightedPathLength contracted + x + y.
Proof.
  intros x y rest contracted.
  revert rest.
  induction contracted as
      [weight|left IHleft right IHright]; intros rest Hfeasible.
  - simpl in Hfeasible.
    pose proof (Permutation_length Hfeasible) as Hlength.
    rewrite length_app in Hlength. simpl in Hlength.
    destruct rest as [|rest_head rest_tail].
    + simpl in Hfeasible.
      assert (weight = x + y).
      {
        apply Permutation_length_1_inv in Hfeasible.
        inversion Hfeasible. reflexivity.
      }
      subst weight.
      exists (HuffmanNode (HuffmanLeaf x) (HuffmanLeaf y)).
      simpl. repeat split; try reflexivity; lia.
    + simpl in Hlength. lia.
  - assert (Hin_merged : In (x + y)
      (HuffmanLeaves left ++ HuffmanLeaves right)).
    {
      eapply Permutation_in.
      - exact Hfeasible.
      - apply in_or_app. right. simpl; auto.
    }
    apply in_app_or in Hin_merged.
    destruct Hin_merged as [Hin_left|Hin_right].
    + destruct (in_split (x + y) (HuffmanLeaves left) Hin_left) as
        [left_before [left_after Hleft_shape]].
      pose (left_rest := left_before ++ left_after).
      assert (Hleft_perm :
        Permutation (left_rest ++ [x + y]) (HuffmanLeaves left)).
      {
        unfold left_rest. rewrite Hleft_shape.
        rewrite <- app_assoc.
        apply Permutation_app_head.
        apply Permutation_app_comm.
      }
      assert (Hrest_perm :
        Permutation rest (left_rest ++ HuffmanLeaves right)).
      {
        assert (Hleft_front :
          Permutation ((x + y) :: left_rest) (HuffmanLeaves left)).
        {
          eapply Permutation_trans with (l' := left_rest ++ [x + y]).
          - apply Permutation_sym. apply Permutation_app_comm.
          - exact Hleft_perm.
        }
        assert (Hwhole_front :
          Permutation
            ((x + y) :: left_rest ++ HuffmanLeaves right)
            (HuffmanLeaves left ++ HuffmanLeaves right)).
        {
          exact
            (Permutation_app Hleft_front
              (Permutation_refl (HuffmanLeaves right))).
        }
        apply Permutation_cons_inv with (x + y).
        eapply Permutation_trans with (l' := rest ++ [x + y]).
        - apply Permutation_sym. apply Permutation_app_comm.
        - eapply Permutation_trans; [exact Hfeasible|].
          simpl. apply Permutation_sym. exact Hwhole_front.
      }
      destruct (IHleft left_rest Hleft_perm) as
        [expanded_left [Hexpanded_leaves
          [Hexpanded_weight Hexpanded_cost]]].
      exists (HuffmanNode expanded_left right).
      split.
      * simpl.
        eapply Permutation_trans.
        -- apply perm_skip. apply perm_skip. exact Hrest_perm.
        -- exact
             (Permutation_app Hexpanded_leaves
               (Permutation_refl (HuffmanLeaves right))).
      * split; simpl; lia.
    + destruct (in_split (x + y) (HuffmanLeaves right) Hin_right) as
        [right_before [right_after Hright_shape]].
      pose (right_rest := right_before ++ right_after).
      assert (Hright_perm :
        Permutation (right_rest ++ [x + y]) (HuffmanLeaves right)).
      {
        unfold right_rest. rewrite Hright_shape.
        rewrite <- app_assoc.
        apply Permutation_app_head.
        apply Permutation_app_comm.
      }
      assert (Hrest_perm :
        Permutation rest (HuffmanLeaves left ++ right_rest)).
      {
        assert (Hright_front :
          Permutation ((x + y) :: right_rest) (HuffmanLeaves right)).
        {
          eapply Permutation_trans with (l' := right_rest ++ [x + y]).
          - apply Permutation_sym. apply Permutation_app_comm.
          - exact Hright_perm.
        }
        assert (Hwhole_front :
          Permutation
            ((x + y) :: HuffmanLeaves left ++ right_rest)
            (HuffmanLeaves left ++ HuffmanLeaves right)).
        {
          eapply Permutation_trans.
          - apply Permutation_middle.
          - exact
              (Permutation_app
                (Permutation_refl (HuffmanLeaves left)) Hright_front).
        }
        apply Permutation_cons_inv with (x + y).
        eapply Permutation_trans with (l' := rest ++ [x + y]).
        - apply Permutation_sym. apply Permutation_app_comm.
        - eapply Permutation_trans; [exact Hfeasible|].
          simpl. apply Permutation_sym. exact Hwhole_front.
      }
      destruct (IHright right_rest Hright_perm) as
        [expanded_right [Hexpanded_leaves
          [Hexpanded_weight Hexpanded_cost]]].
      exists (HuffmanNode left expanded_right).
      split.
      * simpl.
        eapply Permutation_trans.
        -- apply perm_skip. apply perm_skip. exact Hrest_perm.
        -- eapply Permutation_trans.
           ++ replace
                (x :: y :: HuffmanLeaves left ++ right_rest)
                with (([x; y] ++ HuffmanLeaves left) ++ right_rest)
                by reflexivity.
              replace
                (HuffmanLeaves left ++ x :: y :: right_rest)
                with ((HuffmanLeaves left ++ [x; y]) ++ right_rest).
              2:{ rewrite <- app_assoc. reflexivity. }
              apply Permutation_app_tail.
              apply Permutation_app_comm.
           ++ rewrite <- app_assoc.
              exact
                (Permutation_app
                  (Permutation_refl (HuffmanLeaves left)) Hexpanded_leaves).
      * split; simpl; lia.
Qed.
Lemma huffman_greedy_contraction__merge_transition :
  forall prior x y rest remaining,
    Permutation prior (x :: y :: rest) ->
    (forall weight, In weight prior -> x <= weight) ->
    (forall weight, In weight (y :: rest) -> y <= weight) ->
    HuffmanOptimalCost prior remaining ->
    exists contracted_remaining,
      HuffmanOptimalCost (rest ++ [x + y]) contracted_remaining /\
      remaining = contracted_remaining + x + y.
Proof.
  intros prior x y rest remaining Hprior_perm Hxmin Hymin Hoptimal.
  pose proof
    (huffman_optimal_cost_permutation__merge_transition
      prior (x :: y :: rest) remaining Hprior_perm Hoptimal)
    as Hcanonical_optimal.
  unfold HuffmanOptimalCost, min_value_of_subset,
    min_object_of_subset in Hcanonical_optimal.
  destruct Hcanonical_optimal as
    [best [[Hbest_feasible Hbest_minimal] Hbest_cost]].
  assert (Hbest_node :
    exists left right, best = HuffmanNode left right).
  {
    destruct best as [weight|left right].
    - unfold HuffmanTreeFeasible in Hbest_feasible.
      pose proof (Permutation_length Hbest_feasible) as Hlength.
      simpl in Hlength. lia.
    - exists left, right. reflexivity.
  }
  destruct (huffman_deepest_sibling_exists best Hbest_node) as
    [context [old_first [old_second Hdeepest]]].
  destruct Hdeepest as [Hbest_shape Hdeepest_depth].
  destruct (huffman_normalized_pair_profile__merge_transition
    context old_first old_second) as
    [normalized [depth_tail
      [Hnormalized_leaves [Hnormalized_weight [Hnormalized_cost
        [Hnormalized_height [Hnormalized_depths Hnormalized_relabel]]]]]]].
  assert (Hcanonical_normalized :
    Permutation (x :: y :: rest) (HuffmanLeaves normalized)).
  {
    eapply Permutation_trans; [exact Hbest_feasible|].
    rewrite Hbest_shape.
    apply Permutation_sym. exact Hnormalized_leaves.
  }
  assert (Hnormalized_cost_best :
    HuffmanWeightedPathLength normalized =
      HuffmanWeightedPathLength best).
  {
    rewrite Hbest_shape. exact Hnormalized_cost.
  }
  assert (Hnormalized_depth_shape :
    HuffmanLeafDepths normalized =
      HuffmanTreeHeight normalized ::
        HuffmanTreeHeight normalized :: depth_tail).
  {
    rewrite Hnormalized_depths.
    rewrite Hnormalized_height, <- Hbest_shape, Hdeepest_depth.
    reflexivity.
  }
  assert (Hxcanonical :
    forall weight, In weight (x :: y :: rest) -> x <= weight).
  {
    intros weight Hin.
    apply Hxmin.
    eapply Permutation_in.
    - apply Permutation_sym. exact Hprior_perm.
    - exact Hin.
  }
  assert (Hdepth_nonempty : HuffmanLeafDepths normalized <> []).
  { rewrite Hnormalized_depth_shape. discriminate. }
  pose proof (proj1 (huffman_leaf_depth_profile normalized))
    as Hnormalized_profile_length.
  destruct
    (huffman_two_minima_to_maximum_slots__merge_transition
      x y rest (HuffmanLeaves normalized)
      (HuffmanLeafDepths normalized) (HuffmanTreeHeight normalized)
      Hcanonical_normalized Hxcanonical Hymin Hdepth_nonempty
      Hnormalized_profile_length
      (ex_intro _ depth_tail Hnormalized_depth_shape)
      (huffman_leaf_depths_bounded normalized))
    as [reordered_rest [Hrest_reordered Hexchange_cost]].
  assert (Hrelabel_length :
    length (x :: y :: reordered_rest) =
      length (HuffmanLeaves normalized)).
  {
    pose proof (Permutation_length Hrest_reordered) as Hrest_length.
    pose proof (Permutation_length Hcanonical_normalized) as Htotal_length.
    simpl in Htotal_length |- *. lia.
  }
  destruct (Hnormalized_relabel
    (x :: y :: reordered_rest) Hrelabel_length) as
    [relabeled [Hrelabeled_leaves [Hrelabeled_weight
      [Hrelabeled_profile Hrelabeled_contract]]]].
  destruct (Hrelabeled_contract x y reordered_rest eq_refl) as
    [contracted [Hcontracted_leaves
      [Hcontracted_weight Hcontracted_cost]]].
  assert (Hrelabeled_feasible :
    HuffmanTreeFeasible (x :: y :: rest) relabeled).
  {
    unfold HuffmanTreeFeasible.
    rewrite Hrelabeled_leaves.
    apply perm_skip. apply perm_skip. exact Hrest_reordered.
  }
  pose proof (proj2 (huffman_leaf_depth_profile normalized))
    as Hnormalized_profile.
  assert (Hrelabeled_le_normalized :
    HuffmanWeightedPathLength relabeled <=
      HuffmanWeightedPathLength normalized).
  {
    rewrite <- Hrelabeled_profile, <- Hnormalized_profile.
    exact Hexchange_cost.
  }
  pose proof (Hbest_minimal relabeled Hrelabeled_feasible)
    as Hbest_le_relabeled.
  assert (Hrelabeled_cost_best :
    HuffmanWeightedPathLength relabeled =
      HuffmanWeightedPathLength best) by lia.
  exists (HuffmanWeightedPathLength contracted).
  split.
  - unfold HuffmanOptimalCost, min_value_of_subset,
      min_object_of_subset.
    exists contracted.
    split; [split|reflexivity].
    + unfold HuffmanTreeFeasible.
      eapply Permutation_trans.
      * apply Permutation_app; [exact Hrest_reordered|reflexivity].
      * eapply Permutation_trans.
        -- apply Permutation_app_comm.
        -- rewrite Hcontracted_leaves. reflexivity.
    + intros candidate Hcandidate_feasible.
      unfold HuffmanTreeFeasible in Hcandidate_feasible.
      destruct (huffman_expand_contracted_tree__merge_transition
        x y rest candidate Hcandidate_feasible) as
        [expanded [Hexpanded_feasible
          [Hexpanded_weight Hexpanded_cost]]].
      pose proof (Hbest_minimal expanded Hexpanded_feasible)
        as Hbest_le_expanded.
      lia.
  - lia.
Qed.
Lemma replace_nth_decomposition__merge_transition :
  forall (A : Type) (index : nat) (values : list A) (value : A),
    (index < length values)%nat ->
    replace_nth index values value =
      firstn index values ++ value :: skipn (S index) values.
Proof.
  intros A index values value Hindex.
  revert index Hindex.
  induction values as [|head tail IH]; intros index Hindex;
    simpl in Hindex; try lia.
  destruct index as [|index]; simpl.
  - reflexivity.
  - f_equal. apply IH. lia.
Qed.
Lemma huffman_replace_live_prefix__merge_transition :
  forall (values : list Z) (index value : Z),
    0 <= index < Zlength values ->
    sublist 0 (index + 1) (replace_Znth index value values) =
      sublist 0 index values ++ [value].
Proof.
  intros values index value Hindex.
  unfold sublist, replace_Znth.
  simpl Z.to_nat.
  assert (Hindex_nat :
    (Z.to_nat index < length values)%nat).
  { rewrite Zlength_correct in Hindex. lia. }
  rewrite (replace_nth_decomposition__merge_transition
    _ (Z.to_nat index) values value Hindex_nat).
  assert (Hsuccessor :
    Z.to_nat (index + 1) = S (Z.to_nat index)) by lia.
  rewrite Hsuccessor, firstn_app.
  rewrite firstn_all2.
  2:{ rewrite length_firstn. lia. }
  rewrite length_firstn.
  replace
    (S (Z.to_nat index) - Nat.min (Z.to_nat index) (length values))%nat
    with 1%nat by lia.
  simpl. reflexivity.
Qed.
Lemma sum_permutation__merge_transition :
  forall left right : list Z,
    Permutation left right -> sum left = sum right.
Proof.
  intros left right Hperm.
  induction Hperm; simpl; lia.
Qed.
Lemma huffman_progress_after_merge__merge_transition :
  forall input scratch active x y accumulated,
    0 <= active < Zlength scratch ->
    HuffmanPairReadyLegacy input scratch active x y accumulated ->
    HuffmanProgress input
      (replace_Znth active (x + y) scratch)
      (active + 1) (accumulated + x + y).
Proof.
  intros input scratch active x y accumulated Hactive Hpair.
  unfold HuffmanPairReadyLegacy in Hpair.
  destruct Hpair as
    [prior [Hprior [Hxminimum [Hyminimum Hresidual]]]].
  unfold HuffmanResidualOptimum in Hresidual.
  destruct Hresidual as
    [Hprior_sum [remaining [Hprior_optimal Hinput_optimal]]].
  destruct (huffman_greedy_contraction__merge_transition
    prior x y (sublist 0 active scratch) remaining
    Hprior Hxminimum Hyminimum Hprior_optimal) as
    [contracted_remaining [Hcontracted_optimal Hremaining]].
  unfold HuffmanProgress, HuffmanResidualOptimum.
  rewrite huffman_replace_live_prefix__merge_transition by exact Hactive.
  split.
  - rewrite sum_app. simpl.
    pose proof (sum_permutation__merge_transition _ _ Hprior)
      as Hprior_permutation_sum.
    simpl in Hprior_permutation_sum.
    lia.
  - exists contracted_remaining.
    split; [exact Hcontracted_optimal|].
    replace
      (accumulated + x + y + contracted_remaining)
      with (accumulated + remaining) by lia.
    exact Hinput_optimal.
Qed.
Lemma huffman_leaves_nonempty__final_result :
  forall tree, (1 <= length (HuffmanLeaves tree))%nat.
Proof.
  induction tree; simpl.
  - lia.
  - rewrite length_app. lia.
Qed.
Lemma huffman_singleton_tree_cost_zero__final_result :
  forall weight tree,
    HuffmanTreeFeasible [weight] tree ->
    HuffmanWeightedPathLength tree = 0.
Proof.
  intros weight tree Hfeasible.
  destruct tree as [leaf_weight | left_tree right_tree]; simpl; auto.
  unfold HuffmanTreeFeasible in Hfeasible.
  pose proof (Permutation_length Hfeasible) as Hlength.
  simpl in Hlength.
  rewrite length_app in Hlength.
  pose proof (huffman_leaves_nonempty__final_result left_tree).
  pose proof (huffman_leaves_nonempty__final_result right_tree).
  lia.
Qed.
Lemma huffman_singleton_optimal_zero__final_result :
  forall weight answer,
    HuffmanOptimalCost [weight] answer ->
    answer = 0.
Proof.
  intros weight answer Hoptimal.
  unfold HuffmanOptimalCost, min_value_of_subset,
    min_object_of_subset in Hoptimal.
  destruct Hoptimal as [tree [[Hfeasible _] Hanswer]].
  rewrite <- Hanswer.
  apply (huffman_singleton_tree_cost_zero__final_result weight tree).
  exact Hfeasible.
Qed.
Lemma sublist_zero_one__final_result :
  forall values : list Z,
    1 <= Zlength values ->
    sublist 0 1 values = [Znth 0 values 0].
Proof.
  intros values Hlength.
  pose proof (sublist_single 0 0 values) as Hsingle.
  replace (0 + 1) with 1 in Hsingle by lia.
  apply Hsingle.
  lia.
Qed.

(** Public selection facts use the same library minimum as the final optimum.
    The prefix is the mathematical candidate domain; all storage and machine
    constraints remain explicit in the C annotations. *)
Definition HuffmanMinScan (scratch : list Z) (scanned best : Z) : Prop :=
  min_value_of_subset Z.le
    (fun k : Z => 0 <= k < scanned)
    (fun k => Znth k scratch 0) (Znth best scratch 0).

Definition HuffmanFirstHeld (input scratch : list Z)
    (active held accumulated : Z) : Prop :=
  exists prior_live,
    Permutation prior_live (held :: sublist 0 active scratch) /\
    min_value_of_subset Z.le (fun weight => In weight prior_live)
      (fun weight : Z => weight) held /\
    HuffmanResidualOptimum input prior_live accumulated.

Definition HuffmanPairReady (input scratch : list Z)
    (active first second accumulated : Z) : Prop :=
  exists prior_live,
    Permutation prior_live (first :: second :: sublist 0 active scratch) /\
    min_value_of_subset Z.le (fun weight => In weight prior_live)
      (fun weight : Z => weight) first /\
    min_value_of_subset Z.le
      (fun weight => In weight (second :: sublist 0 active scratch))
      (fun weight : Z => weight) second /\
    HuffmanResidualOptimum input prior_live accumulated.

Lemma huffman_scan_iff scratch scanned best :
  0 <= best < scanned ->
  (HuffmanMinScan scratch scanned best <->
   HuffmanMinScanLegacy scratch scanned best).
Proof.
  intros Hbest. unfold HuffmanMinScan, HuffmanMinScanLegacy,
    min_value_of_subset, min_object_of_subset.
  split.
  - intros [k [[Hk Hmin] Heq]] j Hj. rewrite <- Heq. apply Hmin, Hj.
  - intros Hmin. exists best. repeat split; auto; lia.
Qed.

Lemma huffman_value_minimum_iff values best :
  In best values ->
  (min_value_of_subset Z.le (fun value => In value values)
    (fun value : Z => value) best <->
   (forall value, In value values -> best <= value)).
Proof.
  intros Hin. unfold min_value_of_subset, min_object_of_subset.
  split.
  - intros [value [[Hv Hmin] ->]]. exact Hmin.
  - intros Hmin. exists best. auto.
Qed.

Lemma huffman_first_held_iff input scratch active held accumulated :
  HuffmanFirstHeld input scratch active held accumulated <->
  HuffmanFirstHeldLegacy input scratch active held accumulated.
Proof.
  unfold HuffmanFirstHeld, HuffmanFirstHeldLegacy.
  assert (Hmember : forall prior,
    Permutation prior (held :: sublist 0 active scratch) -> In held prior).
  { intros prior Hp. eapply Permutation_in; [apply Permutation_sym, Hp|]. simpl; auto. }
  split; intros [prior [Hp [Hm Hr]]]; exists prior; split; [exact Hp| |exact Hp|];
    split; try exact Hr.
  - apply (proj1 (huffman_value_minimum_iff prior held (Hmember prior Hp))), Hm.
  - apply (proj2 (huffman_value_minimum_iff prior held (Hmember prior Hp))), Hm.
Qed.

Lemma huffman_pair_ready_iff input scratch active first second accumulated :
  HuffmanPairReady input scratch active first second accumulated <->
  HuffmanPairReadyLegacy input scratch active first second accumulated.
Proof.
  unfold HuffmanPairReady, HuffmanPairReadyLegacy.
  assert (Hmember : forall prior,
    Permutation prior (first :: second :: sublist 0 active scratch) -> In first prior).
  { intros prior Hp. eapply Permutation_in; [apply Permutation_sym, Hp|]. simpl; auto. }
  split; intros [prior [Hp [Hf [Hs Hr]]]]; exists prior;
    split; [exact Hp| |exact Hp|]; split.
  - apply (proj1 (huffman_value_minimum_iff prior first (Hmember prior Hp))), Hf.
  - split; [|exact Hr].
    apply (proj1 (huffman_value_minimum_iff (second :: sublist 0 active scratch) second (or_introl eq_refl))), Hs.
  - apply (proj2 (huffman_value_minimum_iff prior first (Hmember prior Hp))), Hf.
  - split; [|exact Hr].
    apply (proj2 (huffman_value_minimum_iff (second :: sublist 0 active scratch) second (or_introl eq_refl))), Hs.
Qed.

Lemma huffman_input_bounds_iff weights :
  HuffmanInputBounded weights <->
  Forall (Z.le 1) weights /\ Forall (Z.ge 1000) weights.
Proof.
  unfold HuffmanInputBounded.
  rewrite !(Forall_Znth _ 0). setoid_rewrite Z.ge_le_iff. split.
  - intros H. split; intros i Hi; specialize (H i Hi); lia.
  - intros [Hl Hu] i Hi. specialize (Hl i Hi). specialize (Hu i Hi). lia.
Qed.

Lemma huffman_prefix_forall_iff (P : Z -> Prop) values active :
  0 <= active <= Zlength values ->
  (Forall P (sublist 0 active values) <->
   forall k, 0 <= k < active -> P (Znth k values 0)).
Proof.
  intros Hactive. rewrite (Forall_Znth _ 0).
  rewrite Zlength_sublist0 by exact Hactive.
  split; intros H k Hk.
  - specialize (H k Hk). rewrite Znth_sublist0 in H by lia. exact H.
  - rewrite Znth_sublist0 by lia. apply H, Hk.
Qed.
