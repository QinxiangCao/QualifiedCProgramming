Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition OneEqualPairDeletion (before after : list Z) : Prop :=
  exists i,
    0 <= i < Zlength before - 1 /\
    Znth i before 0 = Znth (i + 1) before 0 /\
    after = sublist 0 i before ++ sublist (i + 2) (Zlength before) before.

Definition DeletionGameTrace (initial : list Z) (states : list (list Z)) : Prop :=
  0 < Zlength states /\ Znth 0 states [] = initial /\
  (forall k, 0 <= k < Zlength states - 1 ->
     OneEqualPairDeletion (Znth k states []) (Znth (k + 1) states [])) /\
  (forall next,
     ~ OneEqualPairDeletion (Znth (Zlength states - 1) states []) next).

Definition FollowsDeletionStrategy
    (turn_parity : bool)
    (strategy : list (list Z) -> list Z)
    (states : list (list Z)) : Prop :=
  forall k, 0 <= k < Zlength states - 1 ->
    Z.even k = turn_parity ->
    Znth (k + 1) states [] = strategy (sublist 0 (k + 1) states).

Definition FirstPlayerWinsDeletionGame (s : list Z) : Prop :=
  forall states,
    DeletionGameTrace s states ->
    Z.even (Zlength states - 1) = false.

Definition PairDeletionTraceTo
    (initial final : list Z) (moves : Z) : Prop :=
  0 <= moves /\
  exists states,
    Zlength states = moves + 1 /\
    Znth 0 states [] = initial /\
    Znth moves states [] = final /\
    (forall k, 0 <= k < moves ->
       OneEqualPairDeletion (Znth k states []) (Znth (k + 1) states [])).

Definition PairDeletionIrreducible (s : list Z) : Prop :=
  forall next, ~ OneEqualPairDeletion s next.

Definition PrefixGameState
    (prefix reduced : list Z) (moves : Z) : Prop :=
  PairDeletionTraceTo prefix reduced moves /\
  PairDeletionIrreducible reduced /\
  (forall states,
     DeletionGameTrace prefix states ->
     Zlength states = moves + 1).

Definition Pre (s : list Z) : Prop :=
  1 <= Zlength s <= 100000 /\
  Forall (fun c => 97 <= c <= 122) s.

Definition Spec (s : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\ (out = 1 <-> FirstPlayerWinsDeletionGame s).

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Lemma one_equal_pair_deletion_decompose__stack_transitions :
  forall before after,
    OneEqualPairDeletion before after ->
    exists l c r, before = l ++ c :: c :: r /\ after = l ++ r.
Proof.
  intros before after (i & Hi & Heq & Hafter).
  exists (sublist 0 i before), (Znth i before 0),
    (sublist (i + 2) (Zlength before) before).
  split; [|exact Hafter].
  rewrite <- (sublist_self before (Zlength before) eq_refl) at 1.
  rewrite (sublist_split 0 (Zlength before) i) by lia.
  rewrite (sublist_split i (Zlength before) (i + 1)) by lia.
  rewrite (sublist_split (i + 1) (Zlength before) (i + 2)) by lia.
  rewrite (sublist_single 0 i before) by lia.
  replace (i + 2) with ((i + 1) + 1) by lia.
  rewrite (sublist_single 0 (i + 1) before) by lia.
  rewrite <- Heq.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.
Lemma one_equal_pair_deletion_length__stack_transitions :
  forall before after,
    OneEqualPairDeletion before after ->
    Zlength after = Zlength before - 2.
Proof.
  intros before after Hdel.
  destruct (one_equal_pair_deletion_decompose__stack_transitions _ _ Hdel)
    as (l & c & r & -> & ->).
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  simpl.
  lia.
Qed.
Lemma pair_deletion_irreducible_adjacent__stack_transitions :
  forall s,
    PairDeletionIrreducible s <->
    forall i, 0 <= i < Zlength s - 1 -> Znth i s 0 <> Znth (i + 1) s 0.
Proof.
  intros s; split.
  - intros Hirred i Hi Heq.
    specialize (Hirred
      (sublist 0 i s ++ sublist (i + 2) (Zlength s) s)).
    apply Hirred.
    exists i; auto.
  - intros Hadj next (i & Hi & Heq & Hnext).
    apply (Hadj i Hi Heq).
Qed.
Lemma pair_deletion_irreducible_tail__stack_transitions :
  forall a s,
    PairDeletionIrreducible (a :: s) -> PairDeletionIrreducible s.
Proof.
  intros a s Hirred.
  apply (proj2 (pair_deletion_irreducible_adjacent__stack_transitions s)).
  pose proof
    (proj1 (pair_deletion_irreducible_adjacent__stack_transitions (a :: s)) Hirred)
    as Hadj.
  intros i Hi.
  specialize (Hadj (i + 1)).
  rewrite Zlength_cons in Hadj.
  specialize (Hadj ltac:(lia)).
  rewrite (Znth_cons 0 (i + 1)) in Hadj by lia.
  rewrite (Znth_cons 0 ((i + 1) + 1)) in Hadj by lia.
  replace (i + 1 - 1) with i in Hadj by lia.
  replace ((i + 1) + 1 - 1) with (i + 1) in Hadj by lia.
  exact Hadj.
Qed.
Lemma pair_deletion_stack_step_irreducible__stack_transitions :
  forall st c,
    PairDeletionIrreducible st ->
    PairDeletionIrreducible
      ((fun st c =>
          match st with
          | [] => [c]
          | x :: xs => if Z.eq_dec x c then xs else c :: st
          end) st c).
Proof.
  intros st c Hirred.
  destruct st as [|x xs].
  - apply pair_deletion_irreducible_adjacent__stack_transitions.
    intros i Hi. rewrite Zlength_cons in Hi. simpl in Hi. lia.
  - simpl.
    destruct (Z.eq_dec x c) as [->|Hxc].
    + now apply pair_deletion_irreducible_tail__stack_transitions in Hirred.
    + apply (proj2 (pair_deletion_irreducible_adjacent__stack_transitions
        (c :: x :: xs))).
      pose proof
        (proj1 (pair_deletion_irreducible_adjacent__stack_transitions (x :: xs))
          Hirred) as Hadj.
      intros i Hi.
      rewrite !Zlength_cons in Hi.
      destruct (Z.eq_dec i 0) as [->|Hi0].
      * rewrite !Znth0_cons.
        exact (not_eq_sym Hxc).
      * assert (0 < i) by lia.
        rewrite (Znth_cons 0 i) by lia.
        rewrite (Znth_cons 0 (i + 1)) by lia.
        specialize (Hadj (i - 1) ltac:(rewrite Zlength_cons; lia)).
        replace (i - 1 + 1) with i in Hadj by lia.
        replace (i + 1 - 1) with i by lia.
        exact Hadj.
Qed.
Lemma pair_deletion_stack_step_involutive__stack_transitions :
  forall st c,
    PairDeletionIrreducible st ->
    (fun st c =>
       match st with
       | [] => [c]
       | x :: xs => if Z.eq_dec x c then xs else c :: st
       end)
      ((fun st c =>
          match st with
          | [] => [c]
          | x :: xs => if Z.eq_dec x c then xs else c :: st
          end) st c) c = st.
Proof.
  intros st c Hirred.
  destruct st as [|x xs].
  - simpl. destruct (Z.eq_dec c c); congruence.
  - simpl. destruct (Z.eq_dec x c) as [->|Hxc].
    + destruct xs as [|y ys].
      * simpl. destruct (Z.eq_dec c c); congruence.
      * simpl.
        assert (Hcy : c <> y).
        { pose proof
            (proj1 (pair_deletion_irreducible_adjacent__stack_transitions
              (c :: y :: ys)) Hirred) as Hadj.
          specialize (Hadj 0).
          rewrite Zlength_cons in Hadj.
          specialize (Hadj ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg ys); lia)).
          rewrite Znth0_cons in Hadj.
          replace (0 + 1) with 1 in Hadj by lia.
          rewrite (Znth_cons 0 1) in Hadj by lia.
          rewrite Znth0_cons in Hadj.
          exact Hadj. }
        destruct (Z.eq_dec y c); congruence.
    + simpl. destruct (Z.eq_dec c c); congruence.
Qed.
Lemma pair_deletion_fold_irreducible__stack_transitions :
  forall input st,
    PairDeletionIrreducible st ->
    PairDeletionIrreducible
      (fold_left
        (fun st c =>
           match st with
           | [] => [c]
           | x :: xs => if Z.eq_dec x c then xs else c :: st
           end) input st).
Proof.
  induction input as [|a input IH]; intros st Hirred; simpl.
  - exact Hirred.
  - apply IH.
    now apply pair_deletion_stack_step_irreducible__stack_transitions.
Qed.
Lemma one_equal_pair_deletion_fold_invariant__stack_transitions :
  forall before after st,
    OneEqualPairDeletion before after ->
    PairDeletionIrreducible st ->
    fold_left
      (fun st c =>
         match st with
         | [] => [c]
         | x :: xs => if Z.eq_dec x c then xs else c :: st
         end) before st =
    fold_left
      (fun st c =>
         match st with
         | [] => [c]
         | x :: xs => if Z.eq_dec x c then xs else c :: st
         end) after st.
Proof.
  intros before after st Hdel Hirred.
  destruct (one_equal_pair_deletion_decompose__stack_transitions _ _ Hdel)
    as (l & c & r & -> & ->).
  repeat rewrite fold_left_app. simpl.
  rewrite pair_deletion_stack_step_involutive__stack_transitions.
  - reflexivity.
  - now apply pair_deletion_fold_irreducible__stack_transitions.
Qed.
Lemma pair_deletion_fold_irreducible_word__stack_transitions :
  forall s st,
    PairDeletionIrreducible s ->
    (match st, s with
     | x :: _, a :: _ => x <> a
     | _, _ => True
     end) ->
    fold_left
      (fun st c =>
         match st with
         | [] => [c]
         | x :: xs => if Z.eq_dec x c then xs else c :: st
         end) s st = rev s ++ st.
Proof.
  induction s as [|a s IH]; intros st Hirred Hboundary.
  - reflexivity.
  - assert (Htail : PairDeletionIrreducible s).
    { now apply (pair_deletion_irreducible_tail__stack_transitions a). }
    assert (Hnext :
      match a :: st, s with
      | x :: _, b :: _ => x <> b
      | _, _ => True
      end).
    { destruct s as [|b t]; [exact I|].
      simpl.
      pose proof
        (proj1 (pair_deletion_irreducible_adjacent__stack_transitions
          (a :: b :: t)) Hirred) as Hadj.
      specialize (Hadj 0).
      rewrite Zlength_cons in Hadj.
      specialize (Hadj ltac:(rewrite Zlength_cons;
        pose proof (Zlength_nonneg t); lia)).
      rewrite Znth0_cons in Hadj.
      replace (0 + 1) with 1 in Hadj by lia.
      rewrite (Znth_cons 0 1) in Hadj by lia.
      rewrite Znth0_cons in Hadj.
      exact Hadj. }
    simpl.
    destruct st as [|x xs].
    + rewrite (IH [a] Htail Hnext).
      rewrite app_nil_r. reflexivity.
    + simpl in Hboundary.
      destruct (Z.eq_dec x a) as [Hxa|Hxa]; [contradiction|].
      rewrite (IH (a :: x :: xs) Htail Hnext).
      rewrite <- app_assoc. reflexivity.
Qed.
Lemma pair_deletion_fold_irreducible_empty__stack_transitions :
  forall s,
    PairDeletionIrreducible s ->
    fold_left
      (fun st c =>
         match st with
         | [] => [c]
         | x :: xs => if Z.eq_dec x c then xs else c :: st
         end) s [] = rev s.
Proof.
  intros s Hirred.
  pose proof (pair_deletion_fold_irreducible_word__stack_transitions
    s [] Hirred I) as H.
  now rewrite app_nil_r in H.
Qed.
Lemma pair_deletion_states_invariant_nat__stack_transitions :
  forall n states,
    Zlength states = Z.of_nat n + 1 ->
    (forall k, 0 <= k < Z.of_nat n ->
      OneEqualPairDeletion (Znth k states []) (Znth (k + 1) states [])) ->
    fold_left
      (fun st c =>
         match st with
         | [] => [c]
         | x :: xs => if Z.eq_dec x c then xs else c :: st
         end) (Znth 0 states []) [] =
    fold_left
      (fun st c =>
         match st with
         | [] => [c]
         | x :: xs => if Z.eq_dec x c then xs else c :: st
         end) (Znth (Z.of_nat n) states []) [] /\
    Zlength (Znth 0 states []) =
      Zlength (Znth (Z.of_nat n) states []) + 2 * Z.of_nat n.
Proof.
  induction n as [|n IH]; intros states Hlen Hsteps.
  - simpl. split; [reflexivity|lia].
  - destruct states as [|s0 rest].
    { change (0 = Z.of_nat (S n) + 1) in Hlen.
      rewrite Nat2Z.inj_succ in Hlen.
      pose proof (Nat2Z.is_nonneg n). lia. }
    destruct rest as [|s1 tail].
    { change (1 = Z.of_nat (S n) + 1) in Hlen.
      rewrite Nat2Z.inj_succ in Hlen.
      pose proof (Nat2Z.is_nonneg n). lia. }
    assert (Hfirst : OneEqualPairDeletion s0 s1).
    { specialize (Hsteps 0 ltac:(lia)).
      rewrite Znth0_cons in Hsteps.
      replace (0 + 1) with 1 in Hsteps by lia.
      rewrite (Znth_cons [] 1) in Hsteps by lia.
      rewrite Znth0_cons in Hsteps.
      exact Hsteps. }
    assert (Htail_len : Zlength (s1 :: tail) = Z.of_nat n + 1).
    { rewrite !Zlength_cons in Hlen. rewrite Nat2Z.inj_succ in Hlen.
      rewrite Zlength_cons. unfold Z.succ in Hlen |- *. lia. }
    assert (Htail_steps : forall k, 0 <= k < Z.of_nat n ->
      OneEqualPairDeletion
        (Znth k (s1 :: tail) []) (Znth (k + 1) (s1 :: tail) [])).
    { intros k Hk.
      specialize (Hsteps (k + 1) ltac:(simpl; lia)).
      rewrite (Znth_cons [] (k + 1)) in Hsteps by lia.
      rewrite (Znth_cons [] ((k + 1) + 1)) in Hsteps by lia.
      replace (k + 1 - 1) with k in Hsteps by lia.
      replace (k + 1 + 1 - 1) with (k + 1) in Hsteps by lia.
      exact Hsteps. }
    specialize (IH (s1 :: tail) Htail_len Htail_steps).
    destruct IH as [IHfold IHlen].
    split.
    + rewrite Znth0_cons, (Znth_cons [] (Z.of_nat (S n))) by lia.
      replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
      transitivity
        (fold_left
          (fun st c =>
             match st with
             | [] => [c]
             | x :: xs => if Z.eq_dec x c then xs else c :: st
             end) s1 []).
      * apply one_equal_pair_deletion_fold_invariant__stack_transitions;
          [exact Hfirst|].
        apply (proj2 (pair_deletion_irreducible_adjacent__stack_transitions [])).
        intros k Hk. simpl in Hk. lia.
      * rewrite Znth0_cons in IHfold. exact IHfold.
    + rewrite Znth0_cons, (Znth_cons [] (Z.of_nat (S n))) by lia.
      replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
      rewrite Znth0_cons in IHlen.
      pose proof (one_equal_pair_deletion_length__stack_transitions _ _ Hfirst)
        as Hfirst_len.
      lia.
Qed.
Lemma pair_deletion_trace_invariants__stack_transitions :
  forall initial final moves,
    PairDeletionTraceTo initial final moves ->
    fold_left
      (fun st c =>
         match st with
         | [] => [c]
         | x :: xs => if Z.eq_dec x c then xs else c :: st
         end) initial [] =
    fold_left
      (fun st c =>
         match st with
         | [] => [c]
         | x :: xs => if Z.eq_dec x c then xs else c :: st
         end) final [] /\
    Zlength initial = Zlength final + 2 * moves.
Proof.
  intros initial final moves
    (Hmoves & states & Hlen & Hfirst & Hlast & Hsteps).
  remember (Z.to_nat moves) as n eqn:Hn.
  assert (Hmoves_nat : moves = Z.of_nat n).
  { subst n. rewrite Z2Nat.id by lia. reflexivity. }
  pose proof (pair_deletion_states_invariant_nat__stack_transitions
    n states ltac:(lia) ltac:(intros; apply Hsteps; lia)) as Hinv.
  rewrite Hfirst in Hinv.
  rewrite <- Hmoves_nat in Hinv.
  rewrite Hlast in Hinv.
  exact Hinv.
Qed.
Lemma pair_deletion_normal_form_unique__stack_transitions :
  forall initial final1 moves1 final2 moves2,
    PairDeletionTraceTo initial final1 moves1 ->
    PairDeletionIrreducible final1 ->
    PairDeletionTraceTo initial final2 moves2 ->
    PairDeletionIrreducible final2 ->
    final1 = final2 /\ moves1 = moves2.
Proof.
  intros initial final1 moves1 final2 moves2 Htr1 Hir1 Htr2 Hir2.
  pose proof (pair_deletion_trace_invariants__stack_transitions _ _ _ Htr1)
    as [Hfold1 Hlen1].
  pose proof (pair_deletion_trace_invariants__stack_transitions _ _ _ Htr2)
    as [Hfold2 Hlen2].
  rewrite (pair_deletion_fold_irreducible_empty__stack_transitions _ Hir1)
    in Hfold1.
  rewrite (pair_deletion_fold_irreducible_empty__stack_transitions _ Hir2)
    in Hfold2.
  assert (Hfinal : final1 = final2).
  { apply (f_equal (@rev Z)) in Hfold1.
    apply (f_equal (@rev Z)) in Hfold2.
    rewrite !rev_involutive in Hfold1, Hfold2.
    congruence. }
  subst final2.
  split; [reflexivity|lia].
Qed.
Lemma one_equal_pair_deletion_compose__stack_transitions :
  forall l c r,
    OneEqualPairDeletion (l ++ c :: c :: r) (l ++ r).
Proof.
  intros l c r.
  exists (Zlength l).
  split.
  - repeat rewrite Zlength_app.
    repeat rewrite Zlength_cons.
    pose proof (Zlength_nonneg l).
    pose proof (Zlength_nonneg r).
    simpl. lia.
  - split.
    + rewrite (app_Znth2 0 l (c :: c :: r) (Zlength l)) by lia.
      rewrite (app_Znth2 0 l (c :: c :: r) (Zlength l + 1)) by lia.
      replace (Zlength l - Zlength l) with 0 by lia.
      replace (Zlength l + 1 - Zlength l) with 1 by lia.
      rewrite Znth0_cons.
      rewrite (Znth_cons 0 1) by lia.
      rewrite Znth0_cons. reflexivity.
    + rewrite sublist_app_exact1.
      replace (l ++ c :: c :: r) with ((l ++ [c; c]) ++ r).
      * rewrite sublist_split_app_r with (len := Zlength l + 2).
        -- replace (Zlength l + 2 - (Zlength l + 2)) with 0 by lia.
           replace
             (Zlength ((l ++ [c; c]) ++ r) - (Zlength l + 2))
             with (Zlength r) by
               (repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
                simpl; lia).
           rewrite (sublist_self r (Zlength r) eq_refl).
           reflexivity.
        -- repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
           simpl. lia.
        -- repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
           pose proof (Zlength_nonneg r). simpl. lia.
      * change ((l ++ [c; c]) ++ r = l ++ ([c; c] ++ r)).
        symmetry. apply app_assoc.
Qed.
Lemma one_equal_pair_deletion_append__stack_transitions :
  forall before after suffix,
    OneEqualPairDeletion before after ->
    OneEqualPairDeletion (before ++ suffix) (after ++ suffix).
Proof.
  intros before after suffix Hdel.
  destruct (one_equal_pair_deletion_decompose__stack_transitions _ _ Hdel)
    as (l & c & r & -> & ->).
  repeat rewrite <- app_assoc.
  apply one_equal_pair_deletion_compose__stack_transitions.
Qed.
Lemma Znth_map_in_range__stack_transitions :
  forall (A B : Type) (f : A -> B) l i da,
    0 <= i < Zlength l ->
    Znth i (map f l) (f da) = f (Znth i l da).
Proof.
  intros A B f l i da Hi.
  unfold Znth.
  rewrite map_nth.
  reflexivity.
Qed.
Lemma pair_deletion_trace_append__stack_transitions :
  forall initial final moves suffix,
    PairDeletionTraceTo initial final moves ->
    PairDeletionTraceTo (initial ++ suffix) (final ++ suffix) moves.
Proof.
  intros initial final moves suffix
    (Hmoves & states & Hlen & Hfirst & Hlast & Hsteps).
  split; [exact Hmoves|].
  exists (map (fun s => s ++ suffix) states).
  assert (Hmaplen :
    Zlength (map (fun s => s ++ suffix) states) = Zlength states).
  { repeat rewrite Zlength_correct. now rewrite length_map. }
  split; [lia|].
  split.
  - rewrite (Znth_indep (map (fun s => s ++ suffix) states) 0 [] suffix)
      by lia.
    rewrite Znth_map_in_range__stack_transitions with (da := []) by lia.
    now rewrite Hfirst.
  - split.
    + rewrite (Znth_indep (map (fun s => s ++ suffix) states) moves [] suffix)
        by lia.
      rewrite Znth_map_in_range__stack_transitions with (da := []) by lia.
      now rewrite Hlast.
    + intros k Hk.
      rewrite (Znth_indep (map (fun s => s ++ suffix) states) k [] suffix)
        by lia.
      rewrite (Znth_indep (map (fun s => s ++ suffix) states) (k + 1) [] suffix)
        by lia.
      rewrite !Znth_map_in_range__stack_transitions with (da := []) by lia.
      apply one_equal_pair_deletion_append__stack_transitions.
      now apply Hsteps.
Qed.
Lemma pair_deletion_trace_snoc__stack_transitions :
  forall initial middle final moves,
    PairDeletionTraceTo initial middle moves ->
    OneEqualPairDeletion middle final ->
    PairDeletionTraceTo initial final (moves + 1).
Proof.
  intros initial middle final moves
    (Hmoves & states & Hlen & Hfirst & Hlast & Hsteps) Hdel.
  split; [lia|].
  exists (states ++ [final]).
  split.
  - rewrite Zlength_app, Zlength_cons. simpl. lia.
  - split.
    + rewrite app_Znth1 with (d := []) by lia. exact Hfirst.
    + split.
      * rewrite app_Znth2 with (d := []) by lia.
        replace (moves + 1 - Zlength states) with 0 by lia.
        rewrite Znth0_cons. reflexivity.
      * intros k Hk.
        destruct (Z.eq_dec k moves) as [->|Hkm].
        -- rewrite app_Znth1 with (d := []) by lia.
           replace (moves + 1) with (Zlength states) by lia.
           rewrite app_Znth2 with (d := []) by lia.
           replace (Zlength states - Zlength states) with 0 by lia.
           rewrite Znth0_cons, Hlast. exact Hdel.
        -- assert (k < moves) by lia.
           rewrite !app_Znth1 with (d := []) by lia.
           now apply Hsteps.
Qed.
Lemma deletion_game_trace_to_pair__stack_transitions :
  forall initial states,
    DeletionGameTrace initial states ->
    PairDeletionTraceTo initial
      (Znth (Zlength states - 1) states []) (Zlength states - 1) /\
    PairDeletionIrreducible (Znth (Zlength states - 1) states []).
Proof.
  intros initial states (Hpos & Hfirst & Hsteps & Hirred).
  split.
  - split; [lia|].
    exists states.
    split; [lia|].
    split; [exact Hfirst|].
    split; [reflexivity|].
    intros k Hk. apply Hsteps. lia.
  - exact Hirred.
Qed.
Lemma prefix_game_state_of_normal_trace__stack_transitions :
  forall initial final moves,
    PairDeletionTraceTo initial final moves ->
    PairDeletionIrreducible final ->
    PrefixGameState initial final moves.
Proof.
  intros initial final moves Htrace Hirred.
  split; [exact Htrace|].
  split; [exact Hirred|].
  intros states Hgame.
  destruct (deletion_game_trace_to_pair__stack_transitions _ _ Hgame)
    as [Hother Hother_irred].
  pose proof (pair_deletion_normal_form_unique__stack_transitions
    initial final moves (Znth (Zlength states - 1) states [])
    (Zlength states - 1) Htrace Hirred Hother Hother_irred) as [_ Hmoves].
  lia.
Qed.
Lemma pair_deletion_irreducible_prefix__stack_transitions :
  forall l suffix,
    PairDeletionIrreducible (l ++ suffix) -> PairDeletionIrreducible l.
Proof.
  intros l suffix Hirred.
  apply (proj2 (pair_deletion_irreducible_adjacent__stack_transitions l)).
  pose proof
    (proj1 (pair_deletion_irreducible_adjacent__stack_transitions (l ++ suffix))
      Hirred) as Hadj.
  intros i Hi.
  specialize (Hadj i ltac:(rewrite Zlength_app;
    pose proof (Zlength_nonneg suffix); lia)).
  rewrite !app_Znth1 with (d := 0) in Hadj by lia.
  exact Hadj.
Qed.
Lemma pair_deletion_irreducible_snoc__stack_transitions :
  forall reduced c,
    PairDeletionIrreducible reduced ->
    (reduced = [] \/
      (0 < Zlength reduced /\ Znth (Zlength reduced - 1) reduced 0 <> c)) ->
    PairDeletionIrreducible (reduced ++ [c]).
Proof.
  intros reduced c Hirred [-> | [Hpos Hlast]].
  - apply (proj2 (pair_deletion_irreducible_adjacent__stack_transitions [c])).
    intros i Hi. rewrite Zlength_cons in Hi. simpl in Hi. lia.
  - apply (proj2
      (pair_deletion_irreducible_adjacent__stack_transitions (reduced ++ [c]))).
    pose proof
      (proj1 (pair_deletion_irreducible_adjacent__stack_transitions reduced)
        Hirred) as Hadj.
    intros i Hi.
    rewrite Zlength_app, Zlength_cons in Hi. simpl in Hi.
    destruct (Z_lt_dec i (Zlength reduced - 1)) as [Hinternal|Hboundary].
    + rewrite !app_Znth1 with (d := 0) by lia.
      now apply Hadj.
    + assert (i = Zlength reduced - 1) by lia. subst i.
      rewrite app_Znth1 with (d := 0) by lia.
      rewrite app_Znth2 with (d := 0) by lia.
      replace (Zlength reduced - 1 + 1 - Zlength reduced) with 0 by lia.
      rewrite Znth0_cons. exact Hlast.
Qed.
Lemma list_snoc_as_sublist_last__stack_transitions :
  forall s,
    0 < Zlength s ->
    s = sublist 0 (Zlength s - 1) s ++ [Znth (Zlength s - 1) s 0].
Proof.
  intros s Hpos.
  rewrite <- (sublist_self s (Zlength s) eq_refl) at 1.
  rewrite (sublist_split 0 (Zlength s) (Zlength s - 1)) by lia.
  f_equal.
  replace (sublist (Zlength s - 1) (Zlength s) s)
    with (sublist (Zlength s - 1) ((Zlength s - 1) + 1) s) by
      (f_equal; lia).
  rewrite (sublist_single 0 (Zlength s - 1) s) by lia.
  reflexivity.
Qed.
Lemma prefix_game_state_push__stack_transitions :
  forall prefix reduced moves c,
    PrefixGameState prefix reduced moves ->
    (reduced = [] \/
      (0 < Zlength reduced /\ Znth (Zlength reduced - 1) reduced 0 <> c)) ->
    PrefixGameState (prefix ++ [c]) (reduced ++ [c]) moves.
Proof.
  intros prefix reduced moves c
    (Htrace & Hirred & Hterminal) Hboundary.
  apply prefix_game_state_of_normal_trace__stack_transitions.
  - now apply pair_deletion_trace_append__stack_transitions.
  - now apply pair_deletion_irreducible_snoc__stack_transitions.
Qed.
Lemma prefix_game_state_pop_pair__stack_transitions :
  forall prefix reduced moves c,
    PrefixGameState prefix reduced moves ->
    0 < Zlength reduced ->
    Znth (Zlength reduced - 1) reduced 0 = c ->
    PrefixGameState (prefix ++ [c])
      (sublist 0 (Zlength reduced - 1) reduced) (moves + 1).
Proof.
  intros prefix reduced moves c
    (Htrace & Hirred & Hterminal) Hpos Hlast.
  set (short := sublist 0 (Zlength reduced - 1) reduced).
  assert (Hsnoc : reduced = short ++ [c]).
  { subst short.
    rewrite <- Hlast.
    now apply list_snoc_as_sublist_last__stack_transitions. }
  assert (Hlift : PairDeletionTraceTo
    (prefix ++ [c]) (reduced ++ [c]) moves).
  { now apply pair_deletion_trace_append__stack_transitions. }
  assert (Hdel : OneEqualPairDeletion (reduced ++ [c]) short).
  { rewrite Hsnoc.
    replace ((short ++ [c]) ++ [c]) with (short ++ c :: c :: []).
    - replace short with (short ++ []) at 2 by apply app_nil_r.
      apply one_equal_pair_deletion_compose__stack_transitions.
    - change (short ++ ([c] ++ [c]) = (short ++ [c]) ++ [c]).
      apply app_assoc. }
  apply prefix_game_state_of_normal_trace__stack_transitions.
  - now apply pair_deletion_trace_snoc__stack_transitions with
      (middle := reduced ++ [c]).
  - apply pair_deletion_irreducible_prefix__stack_transitions with
      (suffix := [c]).
    now rewrite <- Hsnoc.
Qed.
Lemma sentinel_nonzero_index_bound__stack_transitions :
  forall text i,
    0 <= i <= Zlength text ->
    Znth i (text ++ [0]) 0 <> 0 ->
    i < Zlength text.
Proof.
  intros text i Hi Hnonzero.
  destruct (Z.eq_dec i (Zlength text)) as [->|Hneq]; [|lia].
  rewrite app_Znth2 with (d := 0) in Hnonzero by lia.
  replace (Zlength text - Zlength text) with 0 in Hnonzero by lia.
  rewrite Znth0_cons in Hnonzero.
  contradiction.
Qed.
Lemma terminator_zero_index_eq_length__final_result :
  forall (text : list Z) (i : Z),
    0 <= i <= Zlength text ->
    (forall j, 0 <= j < Zlength text ->
       97 <= Znth j text 0 <= 122) ->
    Znth i (text ++ [0]) 0 = 0 ->
    i = Zlength text.
Proof.
  intros text i Hibounds Hchars Hzero.
  destruct (Z_lt_ge_dec i (Zlength text)) as [Hlt | Hge]; [| lia].
  rewrite app_Znth1 in Hzero by lia.
  specialize (Hchars i ltac:(lia)).
  lia.
Qed.
Lemma prefix_game_state_spec_parity__final_result :
  forall (prefix reduced : list Z) (moves : Z),
    PrefixGameState prefix reduced moves ->
    Spec prefix (Z.land moves 1).
Proof.
  intros prefix reduced moves Hstate.
  unfold PrefixGameState in Hstate.
  destruct Hstate as [Htrace [Hirreducible Hall]].
  unfold PairDeletionTraceTo in Htrace.
  destruct Htrace as [Hmoves [states [Hlen [Hfirst [Hfinal Hsteps]]]]].
  assert (Hland : Z.land moves 1 = moves mod 2).
  {
    change (Z.land moves (Z.ones 1) = moves mod 2).
    rewrite Z.land_ones by lia.
    reflexivity.
  }
  unfold Spec.
  rewrite Hland.
  split.
  - pose proof (Z.mod_pos_bound moves 2 ltac:(lia)).
    lia.
  - split.
    + intros Hmod states' Hdeletion.
      specialize (Hall states' Hdeletion).
      replace (Zlength states' - 1) with moves by lia.
      pose proof (Z.div_mod moves 2 ltac:(lia)) as Hdecomp.
      rewrite Hmod in Hdecomp.
      replace moves with (2 * (moves / 2) + 1) by lia.
      apply Z.even_odd.
    + intros Hwin.
      assert (Hdeletion : DeletionGameTrace prefix states).
      {
        unfold DeletionGameTrace.
        repeat split.
        - lia.
        - exact Hfirst.
        - intros k Hk.
          apply Hsteps.
          rewrite Hlen in Hk.
          lia.
        - intros next Hnext.
          apply (Hirreducible next).
          rewrite Hlen in Hnext.
          replace (moves + 1 - 1) with moves in Hnext by lia.
          rewrite Hfinal in Hnext.
          exact Hnext.
      }
      specialize (Hwin states Hdeletion).
      rewrite Hlen in Hwin.
      replace (moves + 1 - 1) with moves in Hwin by lia.
      pose proof (Z.mod_pos_bound moves 2 ltac:(lia)) as Hmodbounds.
      assert (Hnotzero : moves mod 2 <> 0).
      {
        intros Hzero.
        pose proof (Z.div_mod moves 2 ltac:(lia)) as Hdecomp.
        rewrite Hzero in Hdecomp.
        replace moves with (2 * (moves / 2)) in Hwin by lia.
        rewrite Z.even_even in Hwin.
        discriminate.
      }
      lia.
Qed.
