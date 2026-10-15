Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition ChainParent (n : Z) (chains : list (list Z)) (p : list Z) : Prop :=
  Zlength p = n /\
  (forall x, 1 <= x <= n -> Znth (x - 1) p 0 = 0 \/ 1 <= Znth (x - 1) p 0 <= n) /\
  (forall ch, In ch chains ->
    (forall i, 0 <= i < Zlength ch - 1 -> Znth (Znth i ch 0 - 1) p 0 = Znth (i + 1) ch 0) /\
    Znth (Znth (Zlength ch - 1) ch 0 - 1) p 0 = 0).
Definition NestStep (n : Z) (p q : list Z) : Prop :=
  exists a b, 1 <= a <= n /\ 1 <= b <= n /\ a <> b /\
   ((Znth (a - 1) p 0 = 0 /\ Znth (b - 1) p 0 = 0 /\
     (forall z, 1 <= z <= n -> Znth (z - 1) p 0 <> b) /\ q = replace_Znth (a - 1) b p) \/
    (Znth (a - 1) p 0 = b /\ Znth (b - 1) p 0 = 0 /\ q = replace_Znth (a - 1) 0 p)).
Definition TargetChain (n : Z) (p : list Z) : Prop :=
  Zlength p = n /\ (forall x, 1 <= x < n -> Znth (x - 1) p 0 = x + 1) /\ Znth (n - 1) p 0 = 0.
Definition ReachMatryoshka (n moves : Z) (chains : list (list Z)) : Prop :=
  exists init st, ChainParent n chains init /\ Zlength st = moves + 1 /\ Znth 0 st [] = init /\
    (forall i, 0 <= i < moves -> NestStep n (Znth i st []) (Znth (i + 1) st [])) /\ TargetChain n (Znth moves st []).
Definition Pre (n : Z) (chains : list (list Z)) : Prop :=
  (* Stated explicitly in the P042 solver Require, so dropped here:
       1 <= n <= 100000 /\
       1 <= Zlength chains <= 100000 /\
       Forall (fun ch => 1 <= Zlength ch <= n) chains. *)
  concat chains <> [] /\
  Permutation (concat chains) (Zrange 1 (n + 1)) /\
  Forall (fun ch => ch <> []) chains /\
  Forall mono_inc chains.

Definition Spec (n : Z) (chains : list (list Z)) (out : Z) : Prop :=
  (min_value_of_subset Z.le (fun d => d >= 0 /\ ReachMatryoshka n d chains) (fun x => x)) out.

(* Row lengths of the chain collection, as the solver receives them in m[]. *)
Definition ChainLengths (chains : list (list Z)) : list Z :=
  map (fun row => Zlength row) chains.

(* A candidate prefix is either the always-usable singleton doll [1], or an
   initial segment [1; ...; q] that is already consecutive in one chain. *)
Definition UsablePrefixCandidate (chains : list (list Z)) (q : Z) : Prop :=
  q = 1 \/
  exists ch,
    In ch chains /\
    1 <= q <= Zlength ch /\
    forall i, 0 <= i < q -> Znth i ch 0 = i + 1.

Definition IsUsablePrefix (chains : list (list Z)) (q : Z) : Prop :=
  UsablePrefixCandidate chains q /\
  forall r, UsablePrefixCandidate chains r -> r <= q.

(* The finite maximum is represented as a mathematical choice, rather than as
   a second implementation of the C input scan. *)
Definition usable_prefix (chains : list (list Z)) : Z :=
  epsilon (inhabits 1) (IsUsablePrefix chains).

(* Cost of extracting every adjacency in the first [upto] chains. *)
Definition PrefixExtractionCost (chains : list (list Z)) (upto : Z) : Z :=
  fold_right Z.add 0
    (map (fun len => len - 1)
      (sublist 0 upto (ChainLengths chains))).

(* Finite, proof-oriented presentation of the maximum used by
   [usable_prefix].  This is only a characterization device: the C scan is not
   reproduced in the functional specification. *)
Fixpoint usable_prefix_upto (chains : list (list Z)) (m : nat) : Z :=
  match m with
  | O => 1
  | S m' =>
      let old := usable_prefix_upto chains m' in
      let q := Z.of_nat (S m') in
      if prop_dec (UsablePrefixCandidate chains q)
      then if Z_le_dec old q then q else old
      else old
  end.

Lemma Zlength_Zrange_aux__matryoshka_minimum : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m; revert low.
  induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.

Lemma Zlength_Zrange__matryoshka_minimum : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__matryoshka_minimum. lia.
Qed.

Lemma Zlength_map__matryoshka_minimum : forall {A B : Type}
    (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.

Lemma Zlength_concat__matryoshka_minimum : forall chains,
  Zlength (concat chains) =
  fold_right Z.add 0 (map (@Zlength Z) chains).
Proof.
  induction chains as [|ch rest IH]; simpl.
  - reflexivity.
  - rewrite Zlength_app, IH. reflexivity.
Qed.

Lemma pre_total_length__matryoshka_minimum : forall n chains,
  1 <= n -> Pre n chains -> Zlength (concat chains) = n.
Proof.
  intros n chains Hn [_ [Hperm _]].
  apply Permutation_length in Hperm.
  apply (f_equal Z.of_nat) in Hperm.
  rewrite <- !Zlength_correct in Hperm.
  rewrite Zlength_Zrange__matryoshka_minimum in Hperm by lia.
  lia.
Qed.

Lemma row_length_bound__matryoshka_minimum : forall n chains ch,
  1 <= n -> Pre n chains -> In ch chains -> Zlength ch <= n.
Proof.
  intros n chains ch Hn Hpre Hin.
  pose proof (pre_total_length__matryoshka_minimum n chains Hn Hpre) as Htotal.
  apply in_split in Hin.
  destruct Hin as [before [after ->]].
  rewrite concat_app in Htotal. simpl in Htotal.
  rewrite !Zlength_app in Htotal.
  pose proof (Zlength_nonneg (concat before)).
  pose proof (Zlength_nonneg (concat after)).
  lia.
Qed.

Lemma usable_prefix_candidate_bound__matryoshka_minimum :
  forall n chains q,
    1 <= n -> Pre n chains -> UsablePrefixCandidate chains q ->
    1 <= q <= n.
Proof.
  intros n chains q Hn Hpre [-> | [ch [Hin [[Hq Hlen] _]]]].
  - lia.
  - split; [exact Hq|].
    eapply Z.le_trans; [exact Hlen|].
    eapply row_length_bound__matryoshka_minimum; eauto.
Qed.

Lemma usable_prefix_upto_candidate__matryoshka_minimum : forall chains m,
  UsablePrefixCandidate chains (usable_prefix_upto chains m).
Proof.
  intros chains m; induction m as [|m IH].
  - left; reflexivity.
  - change (UsablePrefixCandidate chains
      (if prop_dec (UsablePrefixCandidate chains (Z.of_nat (S m)))
       then if Z_le_dec (usable_prefix_upto chains m) (Z.of_nat (S m))
            then Z.of_nat (S m) else usable_prefix_upto chains m
       else usable_prefix_upto chains m)).
    destruct (prop_dec
      (UsablePrefixCandidate chains (Z.of_nat (S m)))) as [Hq|Hq].
    + destruct (Z_le_dec (usable_prefix_upto chains m) (Z.of_nat (S m)));
        [exact Hq|exact IH].
    + exact IH.
Qed.

Lemma usable_prefix_upto_max__matryoshka_minimum : forall chains m q,
  UsablePrefixCandidate chains q ->
  1 <= q <= Z.of_nat m ->
  q <= usable_prefix_upto chains m.
Proof.
  intros chains m; induction m as [|m IH]; intros q Hq Hrange.
  - simpl in Hrange. lia.
  - change (q <=
      (if prop_dec (UsablePrefixCandidate chains (Z.of_nat (S m)))
       then if Z_le_dec (usable_prefix_upto chains m) (Z.of_nat (S m))
            then Z.of_nat (S m) else usable_prefix_upto chains m
       else usable_prefix_upto chains m)).
    destruct (prop_dec
      (UsablePrefixCandidate chains (Z.of_nat (S m)))) as [Htop|Htop].
    + destruct (Z_le_dec (usable_prefix_upto chains m) (Z.of_nat (S m)))
        as [Hle|Hnle].
      * lia.
      * destruct (Z.eq_dec q (Z.of_nat (S m))) as [->|Hneq]; [lia|].
        apply IH; [exact Hq|]. rewrite Nat2Z.inj_succ in Hrange. lia.
    + destruct (Z.eq_dec q (Z.of_nat (S m))) as [Heq|Hneq].
      * subst q; contradiction.
      * apply IH; [exact Hq|]. rewrite Nat2Z.inj_succ in Hrange. lia.
Qed.

Lemma usable_prefix_characterization__matryoshka_minimum : forall n chains,
  1 <= n -> Pre n chains -> IsUsablePrefix chains (usable_prefix chains).
Proof.
  intros n chains Hn Hpre.
  unfold usable_prefix.
  apply epsilon_spec.
  exists (usable_prefix_upto chains (Z.to_nat n)).
  split.
  - apply usable_prefix_upto_candidate__matryoshka_minimum.
  - intros r Hr.
    apply usable_prefix_upto_max__matryoshka_minimum; [exact Hr|].
    rewrite Z2Nat.id by lia.
    eapply usable_prefix_candidate_bound__matryoshka_minimum; eauto.
Qed.

Lemma usable_prefix_bounds__matryoshka_minimum : forall n chains,
  1 <= n -> Pre n chains -> 1 <= usable_prefix chains <= n.
Proof.
  intros n chains Hn Hpre.
  pose proof (usable_prefix_characterization__matryoshka_minimum
                n chains Hn Hpre) as [Hcandidate _].
  eapply usable_prefix_candidate_bound__matryoshka_minimum; eauto.
Qed.

Lemma prefix_extraction_cost_full__matryoshka_minimum : forall chains,
  PrefixExtractionCost chains (Zlength chains) =
  Zlength (concat chains) - Zlength chains.
Proof.
  intros chains.
  unfold PrefixExtractionCost, ChainLengths.
  replace (sublist 0 (Zlength chains)
             (map (fun row : list Z => Zlength row) chains))
    with (map (fun row : list Z => Zlength row) chains).
  2:{
    symmetry.
    rewrite <- (Zlength_map__matryoshka_minimum
      (fun row : list Z => Zlength row) chains).
    pose proof (sublist_app_exact1
      (map (fun row : list Z => Zlength row) chains) []) as Hfull.
    rewrite app_nil_r in Hfull. exact Hfull.
  }
  rewrite Zlength_concat__matryoshka_minimum.
  induction chains as [|ch rest IH]; simpl.
  - reflexivity.
  - rewrite Zlength_cons. lia.
Qed.

(** Proof architecture for the operational part of the minimum theorem.

    Keeping traces inductive separates the local legality of a move from the
    list-indexed encoding used by [ReachMatryoshka].  Construction proofs can
    therefore compose dismantling traces and nesting traces without repeatedly
    rebuilding the [Znth] side conditions. *)
Inductive MatryoshkaTrace (n : Z) :
    list Z -> list (list Z) -> list Z -> Prop :=
| MatryoshkaTrace_refl : forall p,
    MatryoshkaTrace n p [p] p
| MatryoshkaTrace_step : forall p q r st,
    NestStep n p q ->
    MatryoshkaTrace n q st r ->
    MatryoshkaTrace n p (p :: st) r.

Lemma matryoshka_trace_nonempty__operational_architecture :
  forall n p st q,
    MatryoshkaTrace n p st q -> st <> [].
Proof.
  intros n p st q Htrace.
  inversion Htrace; discriminate.
Qed.

Lemma matryoshka_trace_start__operational_architecture :
  forall n p st q,
    MatryoshkaTrace n p st q -> Znth 0 st [] = p.
Proof.
  intros n p st q Htrace.
  inversion Htrace; reflexivity.
Qed.

Lemma matryoshka_trace_end__operational_architecture :
  forall n p st q,
    MatryoshkaTrace n p st q ->
    Znth (Zlength st - 1) st [] = q.
Proof.
  intros n p st q Htrace.
  induction Htrace as [p|p q r st Hstep Htrace IH].
  - reflexivity.
  - replace (Zlength (p :: st) - 1) with (Zlength st)
      by (rewrite Zlength_cons; lia).
    assert (Zlength st > 0) as Hstlen.
    { destruct st as [|s rest].
      - inversion Htrace.
      - rewrite Zlength_cons. pose proof (Zlength_nonneg rest). lia. }
    rewrite Znth_cons by exact Hstlen.
    exact IH.
Qed.

Lemma matryoshka_trace_steps__operational_architecture :
  forall n p st q i,
    MatryoshkaTrace n p st q ->
    0 <= i < Zlength st - 1 ->
    NestStep n (Znth i st []) (Znth (i + 1) st []).
Proof.
  intros n p st q i Htrace.
  revert i.
  induction Htrace as [p|p q r st Hstep Htrace IH]; intros i Hi.
  - rewrite Zlength_cons, Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + change (NestStep n p (Znth 0 st [])).
      rewrite (matryoshka_trace_start__operational_architecture
        n q st r Htrace).
      exact Hstep.
    + assert (0 < i) by lia.
      rewrite !Znth_cons by lia.
      replace (i + 1 - 1) with i by lia.
      replace i with (i - 1 + 1) by lia.
      replace (i - 1 + 1 - 1) with (i - 1) by lia.
      apply (IH (i - 1)). lia.
Qed.

Lemma matryoshka_trace_append__operational_architecture :
  forall n p st q st' r,
    MatryoshkaTrace n p st q ->
    MatryoshkaTrace n q st' r ->
    MatryoshkaTrace n p (st ++ tl st') r.
Proof.
  intros n p st q st' r Hleft Hright.
  induction Hleft as [p|p u q st Hstep Hleft IH].
  - inversion Hright; subst.
    + simpl. constructor.
    + simpl. econstructor; eauto.
  - simpl. econstructor; eauto.
Qed.

(** An attaining construction and a universal lower bound are deliberately
    separate certificates.  The former owns the canonical initial state and
    the dismantle/nest trace; the latter owns the progress and edge-count
    argument over every competing trace. *)
Definition MatryoshkaAttainment
    (n : Z) (chains : list (list Z)) (moves : Z) : Prop :=
  exists init st final,
    ChainParent n chains init /\
    MatryoshkaTrace n init st final /\
    Zlength st = moves + 1 /\
    TargetChain n final.

Definition MatryoshkaLowerBound
    (n : Z) (chains : list (list Z)) (moves : Z) : Prop :=
  forall d, 0 <= d -> ReachMatryoshka n d chains -> moves <= d.

Lemma matryoshka_attainment_reach__operational_architecture :
  forall n chains moves,
    MatryoshkaAttainment n chains moves ->
    ReachMatryoshka n moves chains.
Proof.
  intros n chains moves [init [st [final
    [Hparent [Htrace [Hlength Htarget]]]]]].
  exists init, st.
  split; [exact Hparent|].
  split; [exact Hlength|].
  split.
  - eapply matryoshka_trace_start__operational_architecture; eauto.
  - split.
    + intros i Hi.
      eapply matryoshka_trace_steps__operational_architecture; eauto.
      lia.
    + replace moves with (Zlength st - 1) by lia.
      rewrite (matryoshka_trace_end__operational_architecture
        n init st final Htrace).
      exact Htarget.
Qed.

Lemma matryoshka_certificates_spec__operational_architecture :
  forall n chains moves,
    0 <= moves ->
    MatryoshkaAttainment n chains moves ->
    MatryoshkaLowerBound n chains moves ->
    Spec n chains moves.
Proof.
  intros n chains moves Hmoves Hattain Hlower.
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists moves. split.
  - split.
    + split; [lia|].
      apply matryoshka_attainment_reach__operational_architecture.
      exact Hattain.
    + intros d [Hd Hreach].
      apply Hlower; [lia|exact Hreach].
  - reflexivity.
Qed.

(** Interfaces for the two concrete phases requested by the operational
    proof.  They make the intended canonical-state decomposition explicit;
    concrete proofs can be developed independently and composed with the
    generic lemmas above. *)
Definition MatryoshkaDismantlingPhase
    (n : Z) (chains : list (list Z)) (kept : Z)
    (init middle : list Z) (states : list (list Z)) : Prop :=
  ChainParent n chains init /\
  MatryoshkaTrace n init states middle /\
  Zlength states =
    (Zlength (concat chains) - Zlength chains - (kept - 1)) + 1.

Definition MatryoshkaNestingPhase
    (n kept : Z) (middle final : list Z)
    (states : list (list Z)) : Prop :=
  MatryoshkaTrace n middle states final /\
  Zlength states = (n - kept) + 1 /\
  TargetChain n final.

Lemma matryoshka_phases_attainment__operational_architecture :
  forall n chains kept init middle final dismantle_states nest_states,
    Zlength (concat chains) = n ->
    MatryoshkaDismantlingPhase n chains kept
      init middle dismantle_states ->
    MatryoshkaNestingPhase n kept
      middle final nest_states ->
    MatryoshkaAttainment n chains
      ((n - Zlength chains - (kept - 1)) + (n - kept)).
Proof.
  intros n chains kept init middle final dismantle_states nest_states
    Htotal [Hparent [Hdismantle Hdismantle_len]]
    [Hnest [Hnest_len Htarget]].
  exists init, (dismantle_states ++ tl nest_states), final.
  split; [exact Hparent|].
  split.
  - eapply matryoshka_trace_append__operational_architecture; eauto.
  - split.
    + rewrite Zlength_app.
      destruct nest_states as [|s rest].
      * inversion Hnest.
      * simpl.
        rewrite Hdismantle_len, Htotal.
        rewrite Zlength_cons in Hnest_len.
        lia.
    + exact Htarget.
Qed.

(** Concrete edge-count component of the lower-bound measure. *)
Fixpoint ParentEdgeCount (state : list Z) : Z :=
  match state with
  | [] => 0
  | parent :: rest =>
      (if Z.eq_dec parent 0 then 0 else 1) + ParentEdgeCount rest
  end.

Lemma parent_edge_count_nonnegative__deficit_measure : forall state,
  0 <= ParentEdgeCount state.
Proof.
  induction state as [|parent rest IH]; simpl.
  - lia.
  - destruct (Z.eq_dec parent 0); lia.
Qed.

Lemma parent_edge_count_replace_nth_zero_to_nonzero__deficit_measure :
  forall state index parent,
    (index < length state)%nat ->
    nth index state 0 = 0 ->
    parent <> 0 ->
    ParentEdgeCount (replace_nth index state parent) =
      ParentEdgeCount state + 1.
Proof.
  induction state as [|head rest IH]; intros [|index] parent Hindex Hzero Hparent;
    simpl in *; try lia.
  - subst head.
    destruct (Z.eq_dec parent 0); [contradiction|].
    destruct (Z.eq_dec 0 0); [lia|contradiction].
  - assert ((index < length rest)%nat) as Hindex' by lia.
    pose proof (IH index parent Hindex' Hzero Hparent) as Hrec.
    destruct (Z.eq_dec head 0); rewrite Hrec; lia.
Qed.

Lemma parent_edge_count_replace_nth_nonzero_to_zero__deficit_measure :
  forall state index,
    (index < length state)%nat ->
    nth index state 0 <> 0 ->
    ParentEdgeCount (replace_nth index state 0) =
      ParentEdgeCount state - 1.
Proof.
  induction state as [|head rest IH]; intros [|index] Hindex Hnonzero;
    simpl in *; try lia.
  - destruct (Z.eq_dec head 0); [contradiction|].
    destruct (Z.eq_dec 0 0); [lia|contradiction].
  - assert ((index < length rest)%nat) as Hindex' by lia.
    pose proof (IH index Hindex' Hnonzero) as Hrec.
    destruct (Z.eq_dec head 0); rewrite Hrec; lia.
Qed.

Lemma parent_edge_count_replace_zero_to_nonzero__deficit_measure :
  forall state index parent,
    0 <= index < Zlength state ->
    Znth index state 0 = 0 ->
    parent <> 0 ->
    ParentEdgeCount (replace_Znth index parent state) =
      ParentEdgeCount state + 1.
Proof.
  intros state index parent Hindex Hzero Hparent.
  unfold Znth, replace_Znth in *.
  apply parent_edge_count_replace_nth_zero_to_nonzero__deficit_measure;
    try assumption.
  rewrite Zlength_correct in Hindex. lia.
Qed.

Lemma parent_edge_count_replace_nonzero_to_zero__deficit_measure :
  forall state index,
    0 <= index < Zlength state ->
    Znth index state 0 <> 0 ->
    ParentEdgeCount (replace_Znth index 0 state) =
      ParentEdgeCount state - 1.
Proof.
  intros state index Hindex Hnonzero.
  unfold Znth, replace_Znth in *.
  apply parent_edge_count_replace_nth_nonzero_to_zero__deficit_measure;
    try assumption.
  rewrite Zlength_correct in Hindex. lia.
Qed.

Lemma nest_step_parent_edge_count__deficit_measure :
  forall n before after,
    Zlength before = n ->
    NestStep n before after ->
    ParentEdgeCount after = ParentEdgeCount before + 1 \/
    ParentEdgeCount after = ParentEdgeCount before - 1.
Proof.
  intros n before after Hlength
    [a [b [Ha [Hb [Hab [Hnest|Hunnest]]]]]].
  - left. destruct Hnest as [Ha0 [Hb0 [Hempty ->]]].
    apply parent_edge_count_replace_zero_to_nonzero__deficit_measure.
    + rewrite Hlength. lia.
    + exact Ha0.
    + lia.
  - right. destruct Hunnest as [Habefore [Hb0 ->]].
    apply parent_edge_count_replace_nonzero_to_zero__deficit_measure.
    + rewrite Hlength. lia.
    + rewrite Habefore. lia.
Qed.

(** Consecutive target edges already present from doll [1].  This predicate is
    independent of the maximal-prefix choice and is therefore suitable for
    the per-step lower-bound argument. *)
Definition ConsecutivePrefix (prefix : Z) (state : list Z) : Prop :=
  forall x, 1 <= x < prefix -> Znth (x - 1) state 0 = x + 1.

Lemma nest_step_prefix_backwards__deficit_measure :
  forall n before after prefix,
    Zlength before = n ->
    1 <= prefix <= n ->
    NestStep n before after ->
    ConsecutivePrefix prefix after ->
    ConsecutivePrefix (prefix - 1) before.
Proof.
  intros n before after prefix Hlength Hprefix_bounds
    [a [b [Ha [Hb [Hab [Hnest|Hunnest]]]]]] Hprefix x Hx.
  - destruct Hnest as [Ha0 [Hb0 [Hempty ->]]].
    pose proof (Hprefix x ltac:(lia)) as Hxafter.
    destruct (Z.eq_dec (a - 1) (x - 1)) as [Heq|Hneq].
    + assert (a = x) by lia. subst a.
      rewrite Znth_replace_Znth_Same in Hxafter by
        (rewrite Hlength; lia).
      assert (b = x + 1) by lia. subst b.
      pose proof (Hprefix (x + 1) ltac:(lia)) as Hnext.
      rewrite Znth_replace_Znth_Diff in Hnext.
      * lia.
      * rewrite Hlength; lia.
      * rewrite Hlength; lia.
      * lia.
    + rewrite Znth_replace_Znth_Diff in Hxafter.
      * exact Hxafter.
      * rewrite Hlength; lia.
      * rewrite Hlength; lia.
      * lia.
  - destruct Hunnest as [Habefore [Hb0 ->]].
    pose proof (Hprefix x ltac:(lia)) as Hxafter.
    destruct (Z.eq_dec (a - 1) (x - 1)) as [Heq|Hneq].
    + assert (a = x) by lia. subst a.
      rewrite Znth_replace_Znth_Same in Hxafter by
        (rewrite Hlength; lia).
      lia.
    + rewrite Znth_replace_Znth_Diff in Hxafter.
      * exact Hxafter.
      * rewrite Hlength; lia.
      * rewrite Hlength; lia.
      * lia.
Qed.

Lemma target_chain_consecutive_prefix__deficit_measure : forall n state,
  TargetChain n state -> ConsecutivePrefix n state.
Proof.
  intros n state [_ [Hprefix _]] x Hx.
  apply Hprefix. lia.
Qed.

Lemma parent_edge_count_all_but_last__deficit_measure : forall state,
  state <> [] ->
  (forall i, 0 <= i < Zlength state - 1 -> Znth i state 0 <> 0) ->
  Znth (Zlength state - 1) state 0 = 0 ->
  ParentEdgeCount state = Zlength state - 1.
Proof.
  induction state as [|head tail IH]; intros Hnonempty Hall Hlast.
  - contradiction.
  - destruct tail as [|second rest].
    + simpl in Hlast |- *.
      change (head = 0) in Hlast. subst head.
      destruct (Z.eq_dec 0 0); [lia|contradiction].
    + assert (head <> 0) as Hhead.
      { apply (Hall 0). rewrite !Zlength_cons. pose proof (Zlength_nonneg rest). lia. }
      assert (forall i, 0 <= i < Zlength (second :: rest) - 1 ->
          Znth i (second :: rest) 0 <> 0) as Htail_all.
      { intros i Hi.
        specialize (Hall (i + 1)).
        rewrite Zlength_cons in Hall.
        rewrite Znth_cons in Hall by lia.
        replace (i + 1 - 1) with i in Hall by lia.
        apply Hall. lia. }
      assert (Znth (Zlength (second :: rest) - 1)
          (second :: rest) 0 = 0) as Htail_last.
      { replace (Zlength (head :: second :: rest) - 1)
          with (Zlength (second :: rest)) in Hlast
          by (rewrite !Zlength_cons; lia).
        rewrite Znth_cons in Hlast by
          (rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia).
        exact Hlast. }
      specialize (IH ltac:(discriminate) Htail_all Htail_last).
      change ((if Z.eq_dec head 0 then 0 else 1) +
        ParentEdgeCount (second :: rest) =
        Zlength (head :: second :: rest) - 1).
      destruct (Z.eq_dec head 0); [contradiction|].
      rewrite IH, !Zlength_cons. lia.
Qed.

Lemma target_chain_parent_edge_count__deficit_measure : forall n state,
  1 <= n -> TargetChain n state -> ParentEdgeCount state = n - 1.
Proof.
  intros n state Hn [Hlength [Hprefix Hlast]].
  assert (state <> []) as Hnonempty.
  { intro Hnil. subst state. change (0 = n) in Hlength. lia. }
  rewrite <- Hlength.
  apply parent_edge_count_all_but_last__deficit_measure.
  - exact Hnonempty.
  - intros i Hi Hzero.
    specialize (Hprefix (i + 1)).
    rewrite Hlength in Hi.
    specialize (Hprefix ltac:(lia)).
    replace (i + 1 - 1) with i in Hprefix by lia.
    lia.
  - rewrite Hlength. exact Hlast.
Qed.

Lemma nest_step_counted_prefix_backwards__deficit_measure :
  forall n before after prefix,
    Zlength before = n ->
    prefix <= n ->
    NestStep n before after ->
    ConsecutivePrefix prefix after ->
    (ParentEdgeCount after = ParentEdgeCount before + 1 /\
       ConsecutivePrefix (prefix - 1) before) \/
    (ParentEdgeCount after = ParentEdgeCount before - 1 /\
       ConsecutivePrefix prefix before).
Proof.
  intros n before after prefix Hlength Hprefix_upper
    [a [b [Ha [Hb [Hab [Hnest|Hunnest]]]]]] Hprefix.
  - left. split.
    + destruct Hnest as [Ha0 [Hb0 [Hempty Hafter]]]. subst after.
      apply parent_edge_count_replace_zero_to_nonzero__deficit_measure.
      * rewrite Hlength. lia.
      * exact Ha0.
      * lia.
    + destruct (Z_le_dec 1 prefix) as [Hprefix_lower|Hprefix_small].
      * eapply nest_step_prefix_backwards__deficit_measure.
        -- exact Hlength.
        -- lia.
        -- exists a, b. split; [exact Ha|].
           split; [exact Hb|].
           split; [exact Hab|].
           left. exact Hnest.
        -- exact Hprefix.
      * intros x Hx. lia.
  - right. split.
    + destruct Hunnest as [Habefore [Hb0 Hafter]]. subst after.
      apply parent_edge_count_replace_nonzero_to_zero__deficit_measure.
      * rewrite Hlength. lia.
      * rewrite Habefore. lia.
    + destruct Hunnest as [Habefore [Hb0 Hafter]]. subst after.
      intros x Hx.
      pose proof (Hprefix x Hx) as Hxafter.
      destruct (Z.eq_dec (a - 1) (x - 1)) as [Heq|Hneq].
      * assert (a = x) by lia. subst a.
        rewrite Znth_replace_Znth_Same in Hxafter by
          (rewrite Hlength; lia).
        lia.
      * rewrite Znth_replace_Znth_Diff in Hxafter.
        -- exact Hxafter.
        -- rewrite Hlength; lia.
        -- rewrite Hlength; lia.
        -- lia.
Qed.

Lemma length_replace_nth__deficit_measure : forall {A : Type}
    (state : list A) index value,
  length (replace_nth index state value) = length state.
Proof.
  intros A state. induction state as [|head rest IH]; intros [|index] value;
    simpl; auto.
Qed.

Lemma Zlength_replace_Znth__deficit_measure : forall {A : Type}
    (state : list A) index value,
  Zlength (replace_Znth index value state) = Zlength state.
Proof.
  intros. rewrite !Zlength_correct.
  unfold replace_Znth. rewrite length_replace_nth__deficit_measure.
  reflexivity.
Qed.

Lemma nest_step_preserves_Zlength__deficit_measure : forall n before after,
  NestStep n before after -> Zlength after = Zlength before.
Proof.
  intros n before after [a [b [Ha [Hb [Hab [Hnest|Hunnest]]]]]].
  - destruct Hnest as [_ [_ [_ ->]]].
    apply Zlength_replace_Znth__deficit_measure.
  - destruct Hunnest as [_ [_ ->]].
    apply Zlength_replace_Znth__deficit_measure.
Qed.

Inductive CountedMatryoshkaTrace (n : Z) :
    list Z -> list (list Z) -> list Z -> Z -> Z -> Prop :=
| CountedMatryoshkaTrace_refl : forall state,
    CountedMatryoshkaTrace n state [state] state 0 0
| CountedMatryoshkaTrace_insert : forall before next final states inserts removals,
    NestStep n before next ->
    ParentEdgeCount next = ParentEdgeCount before + 1 ->
    CountedMatryoshkaTrace n next states final inserts removals ->
    CountedMatryoshkaTrace n before (before :: states) final
      (inserts + 1) removals
| CountedMatryoshkaTrace_remove : forall before next final states inserts removals,
    NestStep n before next ->
    ParentEdgeCount next = ParentEdgeCount before - 1 ->
    CountedMatryoshkaTrace n next states final inserts removals ->
    CountedMatryoshkaTrace n before (before :: states) final
      inserts (removals + 1).

Lemma matryoshka_trace_counted__deficit_measure :
  forall n start states final,
    Zlength start = n ->
    MatryoshkaTrace n start states final ->
    exists inserts removals,
      CountedMatryoshkaTrace n start states final inserts removals.
Proof.
  intros n start states final Hlength Htrace.
  induction Htrace as [state|before next final states Hstep Htrace IH].
  - exists 0, 0. constructor.
  - assert (Zlength next = n) as Hnext_length.
    { rewrite (nest_step_preserves_Zlength__deficit_measure
        n before next Hstep). exact Hlength. }
    specialize (IH Hnext_length).
    destruct IH as [inserts [removals Hcounted]].
    destruct (nest_step_parent_edge_count__deficit_measure
      n before next Hlength Hstep) as [Hinsert|Hremove].
    + exists (inserts + 1), removals.
      econstructor; eauto.
    + exists inserts, (removals + 1).
      econstructor 3; eauto.
Qed.

Lemma counted_trace_counts_nonnegative__deficit_measure :
  forall n start states final inserts removals,
    CountedMatryoshkaTrace n start states final inserts removals ->
    0 <= inserts /\ 0 <= removals.
Proof.
  intros n start states final inserts removals Htrace.
  induction Htrace; lia.
Qed.

Lemma counted_trace_length__deficit_measure :
  forall n start states final inserts removals,
    CountedMatryoshkaTrace n start states final inserts removals ->
    Zlength states = inserts + removals + 1.
Proof.
  intros n start states final inserts removals Htrace.
  induction Htrace.
  - reflexivity.
  - rewrite Zlength_cons, IHHtrace. lia.
  - rewrite Zlength_cons, IHHtrace. lia.
Qed.

Lemma counted_trace_edge_balance__deficit_measure :
  forall n start states final inserts removals,
    CountedMatryoshkaTrace n start states final inserts removals ->
    ParentEdgeCount final =
      ParentEdgeCount start + inserts - removals.
Proof.
  intros n start states final inserts removals Htrace.
  induction Htrace; lia.
Qed.

Lemma counted_trace_prefix_backwards__deficit_measure :
  forall n start states final inserts removals prefix,
    Zlength start = n ->
    prefix <= n ->
    CountedMatryoshkaTrace n start states final inserts removals ->
    ConsecutivePrefix prefix final ->
    ConsecutivePrefix (prefix - inserts) start.
Proof.
  intros n start states final inserts removals prefix
    Hlength Hprefix_upper Htrace.
  induction Htrace as
    [state
    |before next final states inserts removals Hstep Hedge Htrace IH
    |before next final states inserts removals Hstep Hedge Htrace IH];
    intros Hprefix.
  - replace (prefix - 0) with prefix by lia. exact Hprefix.
  - assert (Zlength next = n) as Hnext_length.
    { rewrite (nest_step_preserves_Zlength__deficit_measure
        n before next Hstep). exact Hlength. }
    pose proof (counted_trace_counts_nonnegative__deficit_measure
      n next states final inserts removals Htrace) as [Hinserts _].
    specialize (IH Hnext_length Hprefix).
    destruct (nest_step_counted_prefix_backwards__deficit_measure
      n before next (prefix - inserts) Hlength ltac:(lia) Hstep IH)
      as [[Hedge' Hbefore]|[Hedge' Hbefore]].
    + replace (prefix - (inserts + 1)) with
        (prefix - inserts - 1) by lia.
      exact Hbefore.
    + lia.
  - assert (Zlength next = n) as Hnext_length.
    { rewrite (nest_step_preserves_Zlength__deficit_measure
        n before next Hstep). exact Hlength. }
    pose proof (counted_trace_counts_nonnegative__deficit_measure
      n next states final inserts removals Htrace) as [Hinserts _].
    specialize (IH Hnext_length Hprefix).
    destruct (nest_step_counted_prefix_backwards__deficit_measure
      n before next (prefix - inserts) Hlength ltac:(lia) Hstep IH)
      as [[Hedge' Hbefore]|[Hedge' Hbefore]].
    + lia.
    + exact Hbefore.
Qed.

Lemma counted_trace_candidate_lower_bound__deficit_measure :
  forall n k kept moves init states final inserts removals,
    1 <= n ->
    1 <= kept ->
    Zlength init = n ->
    ParentEdgeCount init = n - k ->
    (forall q, 1 <= q -> ConsecutivePrefix q init -> q <= kept) ->
    CountedMatryoshkaTrace n init states final inserts removals ->
    Zlength states = moves + 1 ->
    TargetChain n final ->
    (n - k - (kept - 1)) + (n - kept) <= moves.
Proof.
  intros n k kept moves init states final inserts removals
    Hn Hkept Hinit_length Hinit_edges Hinit_prefix
    Htrace Hstates_length Htarget.
  pose proof (counted_trace_length__deficit_measure
    n init states final inserts removals Htrace) as Htrace_length.
  pose proof (counted_trace_edge_balance__deficit_measure
    n init states final inserts removals Htrace) as Hedge_balance.
  pose proof (target_chain_parent_edge_count__deficit_measure
    n final Hn Htarget) as Htarget_edges.
  pose proof (target_chain_consecutive_prefix__deficit_measure
    n final Htarget) as Htarget_prefix.
  pose proof (counted_trace_prefix_backwards__deficit_measure
    n init states final inserts removals n Hinit_length ltac:(lia)
      Htrace Htarget_prefix) as Hbackwards_prefix.
  pose proof (counted_trace_counts_nonnegative__deficit_measure
    n init states final inserts removals Htrace) as [Hinserts Hremovals].
  assert (n - kept <= inserts) as Hinserts_needed.
  { destruct (Z_le_dec 1 (n - inserts)) as [Hpositive|Hsmall].
    - specialize (Hinit_prefix (n - inserts) Hpositive Hbackwards_prefix).
      lia.
    - lia. }
  lia.
Qed.

(** Input-encoding facts connecting [Pre]/[ChainParent] to the concrete
    lower-bound profile. *)
Lemma pre_concat_value_bounds__input_profile : forall n chains x,
  Pre n chains -> In x (concat chains) -> 1 <= x <= n.
Proof.
  intros n chains x [_ [Hperm _]] Hin.
  apply (Permutation_in _ Hperm) in Hin.
  rewrite <- In_Zrange in Hin. lia.
Qed.

Lemma pre_row_value_bounds__input_profile : forall n chains row x,
  Pre n chains -> In row chains -> In x row -> 1 <= x <= n.
Proof.
  intros n chains row x Hpre Hrow Hx.
  eapply pre_concat_value_bounds__input_profile; [exact Hpre|].
  apply in_concat. exists row. auto.
Qed.

Lemma pre_row_nonempty_mono__input_profile : forall n chains row,
  Pre n chains -> In row chains -> row <> [] /\ mono_inc row.
Proof.
  intros n chains row [_ [_ [Hnonempty Hmono]]] Hrow.
  rewrite Forall_forall in Hnonempty, Hmono.
  auto.
Qed.

Lemma mono_inc_row_containing_one_starts_one__input_profile :
  forall n chains row,
    Pre n chains -> In row chains -> In 1 row -> Znth 0 row 0 = 1.
Proof.
  intros n chains row Hpre Hrow Hone.
  pose proof (pre_row_nonempty_mono__input_profile
    n chains row Hpre Hrow) as [Hnonempty Hmono].
  destruct (@In_nth Z row 1 0 Hone) as [index [Hindex Hnth]].
  destruct index as [|index].
  - exact Hnth.
  - assert (0 < Z.of_nat (S index)) by lia.
    assert (Z.of_nat (S index) < Zlength row).
    { rewrite Zlength_correct. lia. }
    specialize (Hmono 0 (Z.of_nat (S index)) ltac:(lia)
      ltac:(lia) ltac:(lia)).
    assert (Znth (Z.of_nat (S index)) row 0 = 1) as HnthZ.
    { unfold Znth. rewrite Nat2Z.id. exact Hnth. }
    rewrite HnthZ in Hmono.
    assert (In (Znth 0 row 0) row) as Hhead_in.
    { apply Znth_In_Zlength. lia. }
    pose proof (pre_row_value_bounds__input_profile
      n chains row (Znth 0 row 0) Hpre Hrow Hhead_in).
    lia.
Qed.

Lemma chain_parent_consecutive_row_prefix_nat__input_profile :
  forall n chains init row q,
    1 <= n ->
    Pre n chains ->
    ChainParent n chains init ->
    In row chains ->
    Znth 0 row 0 = 1 ->
    ConsecutivePrefix q init ->
    forall index : nat,
      Z.of_nat index < q ->
      Z.of_nat index < Zlength row /\
      Znth (Z.of_nat index) row 0 = Z.of_nat index + 1.
Proof.
  intros n chains init row q Hn Hpre
    [Hinit_length [Hparent_bounds Hchains]] Hrow Hrow0 Hprefix.
  pose proof (Hchains row Hrow) as [Hinternal Hroot].
  intros index. induction index as [|index IH]; intros Hindexq.
  - split.
    + pose proof (pre_row_nonempty_mono__input_profile
        n chains row Hpre Hrow) as [Hnonempty _].
      destruct row.
      * exfalso. apply Hnonempty. reflexivity.
      * pose proof (Zlength_nonneg row). rewrite Zlength_cons. lia.
    + exact Hrow0.
  - assert (Z.of_nat index < q) as Hprevious_q by lia.
    specialize (IH Hprevious_q) as [Hprevious_len Hprevious_value].
    assert (Z.of_nat index < Zlength row - 1) as Hinternal_index.
    { destruct (Z.eq_dec (Z.of_nat index) (Zlength row - 1)) as [Hlast|Hnotlast].
      - pose proof (Hprefix (Z.of_nat index + 1) ltac:(lia)) as Hprefix_edge.
        replace (Z.of_nat index + 1 - 1) with (Z.of_nat index)
          in Hprefix_edge by lia.
        rewrite <- Hlast in Hroot.
        rewrite Hprevious_value in Hroot.
        replace (Z.of_nat index + 1 - 1) with (Z.of_nat index)
          in Hroot by lia.
        rewrite Hroot in Hprefix_edge. lia.
      - lia. }
    specialize (Hinternal (Z.of_nat index) ltac:(lia)).
    rewrite Hprevious_value in Hinternal.
    replace (Z.of_nat index + 1 - 1) with (Z.of_nat index)
      in Hinternal by lia.
    pose proof (Hprefix (Z.of_nat index + 1) ltac:(lia)) as Hprefix_edge.
    replace (Z.of_nat index + 1 - 1) with (Z.of_nat index)
      in Hprefix_edge by lia.
    rewrite Hprefix_edge in Hinternal.
    split.
    + rewrite Nat2Z.inj_succ.
      change (Z.of_nat index + 1 < Zlength row). lia.
    + rewrite Nat2Z.inj_succ.
      change (Znth (Z.of_nat index + 1) row 0 =
        Z.of_nat index + 1 + 1). lia.
Qed.

Lemma pre_has_row_containing_one__input_profile : forall n chains,
  1 <= n -> Pre n chains ->
  exists row, In row chains /\ In 1 row.
Proof.
  intros n chains Hn [_ [Hperm _]].
  assert (In 1 (Zrange 1 (n + 1))) as Hone.
  { rewrite <- In_Zrange. lia. }
  apply (Permutation_in _ (Permutation_sym Hperm)) in Hone.
  apply in_concat in Hone. exact Hone.
Qed.

Lemma chain_parent_consecutive_prefix_candidate__input_profile :
  forall n chains init q,
    1 <= n ->
    Pre n chains ->
    ChainParent n chains init ->
    1 <= q <= n ->
    ConsecutivePrefix q init ->
    UsablePrefixCandidate chains q.
Proof.
  intros n chains init q Hn Hpre Hparent Hq Hprefix.
  destruct (Z.eq_dec q 1) as [->|Hqneq]; [left; reflexivity|].
  right.
  destruct (pre_has_row_containing_one__input_profile
    n chains Hn Hpre) as [row [Hrow Hone]].
  pose proof (mono_inc_row_containing_one_starts_one__input_profile
    n chains row Hpre Hrow Hone) as Hrow0.
  pose proof (chain_parent_consecutive_row_prefix_nat__input_profile
    n chains init row q Hn Hpre Hparent Hrow Hrow0 Hprefix) as Hnat.
  exists row. split; [exact Hrow|]. split.
  - split; [lia|].
    set (index := Z.to_nat (q - 1)).
    assert (Z.of_nat index = q - 1) as Hindex.
    { unfold index. rewrite Z2Nat.id by lia. reflexivity. }
    specialize (Hnat index ltac:(lia)) as [Hlen _]. lia.
  - intros i Hi.
    set (index := Z.to_nat i).
    assert (Z.of_nat index = i) as Hindex.
    { unfold index. rewrite Z2Nat.id by lia. reflexivity. }
    specialize (Hnat index ltac:(lia)) as [_ Hvalue].
    rewrite Hindex in Hvalue. exact Hvalue.
Qed.

Lemma chain_parent_consecutive_prefix_le_usable__input_profile :
  forall n chains init q,
    1 <= n ->
    Pre n chains ->
    ChainParent n chains init ->
    1 <= q <= n ->
    ConsecutivePrefix q init ->
    q <= usable_prefix chains.
Proof.
  intros n chains init q Hn Hpre Hparent Hq Hprefix.
  pose proof (usable_prefix_characterization__matryoshka_minimum
    n chains Hn Hpre) as [_ Hmax].
  apply Hmax.
  eapply chain_parent_consecutive_prefix_candidate__input_profile; eauto.
Qed.

(** The list-indexed history used by [ReachMatryoshka] is equivalent, in the
    direction needed by the lower bound, to the inductive trace interface. *)
Lemma indexed_history_matryoshka_trace__history_bridge :
  forall n states start final,
    states <> [] ->
    Znth 0 states [] = start ->
    Znth (Zlength states - 1) states [] = final ->
    (forall i, 0 <= i < Zlength states - 1 ->
      NestStep n (Znth i states []) (Znth (i + 1) states [])) ->
    MatryoshkaTrace n start states final.
Proof.
  intros n states. induction states as [|head tail IH];
    intros start final Hnonempty Hstart Hend Hsteps.
  - contradiction.
  - destruct tail as [|next rest].
    + simpl in Hstart, Hend. subst start. subst final. constructor.
    + simpl in Hstart. subst start.
      assert (NestStep n head next) as Hfirst.
      { specialize (Hsteps 0).
        rewrite Znth0_cons, Znth_cons in Hsteps by lia.
        rewrite Znth0_cons in Hsteps.
        apply Hsteps. rewrite !Zlength_cons. pose proof (Zlength_nonneg rest). lia. }
      assert (Znth (Zlength (next :: rest) - 1)
        (next :: rest) [] = final) as Htail_end.
      { replace (Zlength (head :: next :: rest) - 1)
          with (Zlength (next :: rest)) in Hend
          by (rewrite !Zlength_cons; lia).
        rewrite Znth_cons in Hend by
          (rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia).
        exact Hend. }
      assert (forall i, 0 <= i < Zlength (next :: rest) - 1 ->
        NestStep n (Znth i (next :: rest) [])
          (Znth (i + 1) (next :: rest) [])) as Htail_steps.
      { intros i Hi.
        specialize (Hsteps (i + 1)).
        rewrite !Znth_cons in Hsteps by lia.
        assert (Znth (i + 1 + 1) (head :: next :: rest) [] =
          Znth (i + 1) (next :: rest) []) as Hshift.
        { rewrite Znth_cons by lia.
          replace (i + 1 + 1 - 1) with (i + 1) by lia. reflexivity. }
        rewrite Hshift in Hsteps.
        replace (i + 1 - 1) with i in Hsteps by lia.
        replace (i + 1 + 1 - 1) with (i + 1) in Hsteps by lia.
        apply Hsteps. rewrite !Zlength_cons in *. lia. }
      econstructor.
      * exact Hfirst.
      * apply (IH next final); try discriminate; try reflexivity; assumption.
Qed.

Lemma reach_matryoshka_counted_trace__history_bridge :
  forall n moves chains,
    0 <= moves ->
    ReachMatryoshka n moves chains ->
    exists init states final inserts removals,
      ChainParent n chains init /\
      CountedMatryoshkaTrace n init states final inserts removals /\
      Zlength states = moves + 1 /\
      TargetChain n final.
Proof.
  intros n moves chains Hmoves
    [init [states [Hparent [Hlength [Hstart [Hsteps Htarget]]]]]].
  assert (states <> []) as Hnonempty.
  { intro Hnil. subst states. rewrite Zlength_nil in Hlength. lia. }
  set (final := Znth moves states []).
  assert (Znth (Zlength states - 1) states [] = final) as Hend.
  { unfold final. replace (Zlength states - 1) with moves by lia. reflexivity. }
  assert (MatryoshkaTrace n init states final) as Htrace.
  { eapply indexed_history_matryoshka_trace__history_bridge; eauto.
    intros i Hi. apply Hsteps. lia. }
  destruct Hparent as [Hinit_length Hparent_rest].
  destruct (matryoshka_trace_counted__deficit_measure
    n init states final Hinit_length Htrace) as [inserts [removals Hcounted]].
  exists init, states, final, inserts, removals.
  split.
  - split; assumption.
  - split; [exact Hcounted|].
    split; [exact Hlength|].
    unfold final. exact Htarget.
Qed.

Lemma counted_trace_candidate_lower_bound_bounded__history_bridge :
  forall n k kept moves init states final inserts removals,
    1 <= n ->
    1 <= kept ->
    Zlength init = n ->
    ParentEdgeCount init = n - k ->
    (forall q, 1 <= q <= n -> ConsecutivePrefix q init -> q <= kept) ->
    CountedMatryoshkaTrace n init states final inserts removals ->
    Zlength states = moves + 1 ->
    TargetChain n final ->
    (n - k - (kept - 1)) + (n - kept) <= moves.
Proof.
  intros n k kept moves init states final inserts removals
    Hn Hkept Hinit_length Hinit_edges Hinit_prefix
    Htrace Hstates_length Htarget.
  pose proof (counted_trace_length__deficit_measure
    n init states final inserts removals Htrace) as Htrace_length.
  pose proof (counted_trace_edge_balance__deficit_measure
    n init states final inserts removals Htrace) as Hedge_balance.
  pose proof (target_chain_parent_edge_count__deficit_measure
    n final Hn Htarget) as Htarget_edges.
  pose proof (target_chain_consecutive_prefix__deficit_measure
    n final Htarget) as Htarget_prefix.
  pose proof (counted_trace_prefix_backwards__deficit_measure
    n init states final inserts removals n Hinit_length ltac:(lia)
      Htrace Htarget_prefix) as Hbackwards_prefix.
  pose proof (counted_trace_counts_nonnegative__deficit_measure
    n init states final inserts removals Htrace) as [Hinserts Hremovals].
  assert (n - kept <= inserts) as Hinserts_needed.
  { destruct (Z_le_dec 1 (n - inserts)) as [Hpositive|Hsmall].
    - specialize (Hinit_prefix (n - inserts) ltac:(lia)
        Hbackwards_prefix). lia.
    - lia. }
  lia.
Qed.

Lemma matryoshka_candidate_lower_bound_from_edge_profile__history_bridge :
  forall n chains,
    1 <= n ->
    Pre n chains ->
    (forall init, ChainParent n chains init ->
      ParentEdgeCount init = n - Zlength chains) ->
    MatryoshkaLowerBound n chains
      ((n - Zlength chains - (usable_prefix chains - 1)) +
       (n - usable_prefix chains)).
Proof.
  intros n chains Hn Hpre Hedge d Hd Hreach.
  destruct (reach_matryoshka_counted_trace__history_bridge
    n d chains Hd Hreach) as
    [init [states [final [inserts [removals
      [Hparent [Htrace [Hlength Htarget]]]]]]]].
  pose proof Hparent as Hparent_full.
  destruct Hparent as [Hinit_length Hparent_rest].
  pose proof (usable_prefix_bounds__matryoshka_minimum
    n chains Hn Hpre) as Hkept_bounds.
  eapply counted_trace_candidate_lower_bound_bounded__history_bridge;
    try eassumption; try lia.
  - apply Hedge. exact Hparent_full.
  - intros q Hq Hprefix.
    eapply chain_parent_consecutive_prefix_le_usable__input_profile;
      eauto.
Qed.

(** Exact edge profile of the initial parent array. *)
Lemma parent_edge_count_app__input_edges : forall left right,
  ParentEdgeCount (left ++ right) =
  ParentEdgeCount left + ParentEdgeCount right.
Proof.
  intros left right. induction left as [|head tail IH]; simpl; [lia|].
  rewrite IH. lia.
Qed.

Lemma parent_edge_count_permutation__input_edges : forall left right,
  Permutation left right -> ParentEdgeCount left = ParentEdgeCount right.
Proof.
  intros left right Hperm. induction Hperm; simpl; lia.
Qed.

Lemma Znth_Zrange_aux__input_edges : forall m low i,
  0 <= i < Z.of_nat m ->
  Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia|].
  simpl. destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.

Lemma Znth_Zrange__input_edges : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__input_edges by lia. lia.
Qed.

Lemma Znth_map__input_edges : forall {A B : Type}
    (f : A -> B) source (da : A) (db : B) i,
  0 <= i < Zlength source ->
  Znth i (map f source) db = f (Znth i source da).
Proof.
  intros A B f source. induction source as [|head tail IH];
    intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [->|Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.

Lemma map_parent_Zrange_identity__input_edges : forall n state,
  0 <= n -> Zlength state = n ->
  map (fun doll => Znth (doll - 1) state 0) (Zrange 1 (n + 1)) = state.
Proof.
  intros n state Hn Hlength.
  apply nth_ext with (d := 0) (d' := 0).
  - rewrite length_map. apply Nat2Z.inj.
    rewrite <- !Zlength_correct.
    rewrite Zlength_Zrange__matryoshka_minimum by lia. lia.
  - intros index Hindex.
    assert (0 <= Z.of_nat index < n) as Hi.
    { rewrite length_map in Hindex.
      assert (Z.of_nat index < Zlength (Zrange 1 (n + 1))) as Hrange_index.
      { rewrite Zlength_correct. lia. }
      rewrite Zlength_Zrange__matryoshka_minimum in Hrange_index by lia.
      lia. }
    assert (Znth (Z.of_nat index)
      (map (fun doll => Znth (doll - 1) state 0)
        (Zrange 1 (n + 1))) 0 =
      Znth (Z.of_nat index) state 0) as Heq.
    { rewrite (@Znth_map__input_edges Z Z
        (fun doll => Znth (doll - 1) state 0)
        (Zrange 1 (n + 1)) 0 0 (Z.of_nat index)) by
        (rewrite Zlength_Zrange__matryoshka_minimum by lia; lia).
      rewrite Znth_Zrange__input_edges by lia. f_equal. lia. }
    unfold Znth in Heq. rewrite !Nat2Z.id in Heq. exact Heq.
Qed.

Lemma parent_edge_count_mapped_row__input_edges :
  forall n chains init row,
    Pre n chains ->
    ChainParent n chains init ->
    In row chains ->
    ParentEdgeCount
      (map (fun doll => Znth (doll - 1) init 0) row) =
      Zlength row - 1.
Proof.
  intros n chains init row Hpre
    [Hinit_length [Hparent_bounds Hchains]] Hrow.
  pose proof (pre_row_nonempty_mono__input_profile
    n chains row Hpre Hrow) as [Hnonempty Hmono].
  pose proof (Hchains row Hrow) as [Hinternal Hroot].
  rewrite <- (Zlength_map__matryoshka_minimum
    (fun doll => Znth (doll - 1) init 0) row).
  apply parent_edge_count_all_but_last__deficit_measure.
  - destruct row; [contradiction|discriminate].
  - intros i Hi.
    rewrite Zlength_map__matryoshka_minimum in Hi.
    rewrite (@Znth_map__input_edges Z Z
      (fun doll => Znth (doll - 1) init 0) row 0 0 i) by lia.
    rewrite Hinternal by lia.
    pose proof (Znth_In_Zlength row 0 (i + 1) ltac:(lia)) as Hnext_in.
    pose proof (pre_row_value_bounds__input_profile
      n chains row (Znth (i + 1) row 0) Hpre Hrow Hnext_in).
    lia.
  - rewrite Zlength_map__matryoshka_minimum.
    assert (0 < Zlength row) as Hrow_length.
    { destruct row; [contradiction|].
      rewrite Zlength_cons. pose proof (Zlength_nonneg row). lia. }
    rewrite (@Znth_map__input_edges Z Z
      (fun doll => Znth (doll - 1) init 0) row 0 0
      (Zlength row - 1)) by lia.
    exact Hroot.
Qed.

Lemma parent_edge_count_flattened_rows__input_edges :
  forall (rows : list (list Z)) (f : Z -> Z),
  (forall row, In row rows ->
    ParentEdgeCount (map f row) = Zlength row - 1) ->
  ParentEdgeCount (map f (concat rows)) =
    Zlength (concat rows) - Zlength rows.
Proof.
  intros rows. induction rows as [|row rest IH]; intros f Hrows.
  - reflexivity.
  - simpl. rewrite map_app, parent_edge_count_app__input_edges.
    rewrite (Hrows row ltac:(left; reflexivity)).
    rewrite IH.
    + rewrite Zlength_app, !Zlength_cons. lia.
    + intros other Hother. apply Hrows. right. exact Hother.
Qed.

Lemma chain_parent_edge_count__input_edges : forall n chains init,
  1 <= n ->
  Pre n chains ->
  ChainParent n chains init ->
  ParentEdgeCount init = n - Zlength chains.
Proof.
  intros n chains init Hn Hpre Hparent.
  destruct Hpre as [Hconcat [Hperm [Hnonempty Hmono]]].
  assert (Pre n chains) as Hpre_full.
  { repeat split; assumption. }
  pose proof Hparent as Hparent_full.
  destruct Hparent as [Hinit_length Hparent_rest].
  pose proof (Permutation_map
    (fun doll => Znth (doll - 1) init 0) Hperm) as Hmapped_perm.
  rewrite (map_parent_Zrange_identity__input_edges
    n init ltac:(lia) Hinit_length) in Hmapped_perm.
  rewrite <- (parent_edge_count_permutation__input_edges
    _ _ Hmapped_perm).
  rewrite parent_edge_count_flattened_rows__input_edges.
  - pose proof (pre_total_length__matryoshka_minimum
      n chains Hn Hpre_full). lia.
  - intros row Hrow.
    eapply parent_edge_count_mapped_row__input_edges; eauto.
Qed.

Lemma matryoshka_candidate_lower_bound__input_edges : forall n chains,
  1 <= n ->
  Pre n chains ->
  MatryoshkaLowerBound n chains
    ((n - Zlength chains - (usable_prefix chains - 1)) +
     (n - usable_prefix chains)).
Proof.
  intros n chains Hn Hpre.
  eapply matryoshka_candidate_lower_bound_from_edge_profile__history_bridge;
    [exact Hn|exact Hpre|].
  intros init Hparent.
  eapply chain_parent_edge_count__input_edges; eauto.
Qed.

(** Transparent midpoint and the complete increasing-nesting phase. *)
Definition PrefixParentState (n kept : Z) : list Z :=
  map (fun doll => if Z_lt_dec doll kept then doll + 1 else 0)
    (Zrange 1 (n + 1)).

Lemma prefix_parent_state_length__attainment : forall n kept,
  0 <= n -> Zlength (PrefixParentState n kept) = n.
Proof.
  intros n kept Hn. unfold PrefixParentState.
  rewrite Zlength_map__matryoshka_minimum.
  rewrite Zlength_Zrange__matryoshka_minimum by lia. lia.
Qed.

Lemma prefix_parent_state_Znth__attainment : forall n kept doll,
  0 <= n -> 1 <= doll <= n ->
  Znth (doll - 1) (PrefixParentState n kept) 0 =
    if Z_lt_dec doll kept then doll + 1 else 0.
Proof.
  intros n kept doll Hn Hdoll. unfold PrefixParentState.
  rewrite (@Znth_map__input_edges Z Z
    (fun x => if Z_lt_dec x kept then x + 1 else 0)
    (Zrange 1 (n + 1)) 0 0 (doll - 1)) by
    (rewrite Zlength_Zrange__matryoshka_minimum by lia; lia).
  rewrite Znth_Zrange__input_edges by lia.
  replace (1 + (doll - 1)) with doll by lia. reflexivity.
Qed.

Lemma prefix_parent_state_step_replace__attainment :
  forall n current,
    1 <= current < n ->
    replace_Znth (current - 1) (current + 1)
      (PrefixParentState n current) =
    PrefixParentState n (current + 1).
Proof.
  intros n current Hcurrent.
  apply nth_ext with (d := 0) (d' := 0).
  - apply Nat2Z.inj. rewrite <- !Zlength_correct.
    rewrite Zlength_replace_Znth__deficit_measure.
    rewrite !prefix_parent_state_length__attainment by lia. reflexivity.
  - intros index Hindex.
    assert (0 <= Z.of_nat index < n) as Hi.
    { assert (Z.of_nat index < Zlength
        (replace_Znth (current - 1) (current + 1)
          (PrefixParentState n current))) as HindexZ.
      { rewrite Zlength_correct. lia. }
      rewrite Zlength_replace_Znth__deficit_measure,
        prefix_parent_state_length__attainment in HindexZ by lia. lia. }
    assert (Znth (Z.of_nat index)
      (replace_Znth (current - 1) (current + 1)
        (PrefixParentState n current)) 0 =
      Znth (Z.of_nat index) (PrefixParentState n (current + 1)) 0) as Heq.
    { destruct (Z.eq_dec (Z.of_nat index) (current - 1)) as [Heqi|Hneq].
      - rewrite Heqi.
        rewrite Znth_replace_Znth_Same by
          (rewrite prefix_parent_state_length__attainment by lia; lia).
        rewrite (prefix_parent_state_Znth__attainment
          n (current + 1) current) by lia.
        destruct (Z_lt_dec current (current + 1)); lia.
      - rewrite Znth_replace_Znth_Diff by
          (try rewrite prefix_parent_state_length__attainment by lia; lia).
        replace (Z.of_nat index) with (Z.of_nat index + 1 - 1) by lia.
        rewrite (prefix_parent_state_Znth__attainment
          n current (Z.of_nat index + 1)) by lia.
        rewrite (prefix_parent_state_Znth__attainment
          n (current + 1) (Z.of_nat index + 1)) by lia.
        destruct (Z_lt_dec (Z.of_nat index + 1) current);
          destruct (Z_lt_dec (Z.of_nat index + 1) (current + 1)); lia. }
    unfold Znth in Heq. rewrite !Nat2Z.id in Heq. exact Heq.
Qed.

Lemma prefix_parent_state_nest_step__attainment : forall n current,
  1 <= current < n ->
  NestStep n (PrefixParentState n current)
    (PrefixParentState n (current + 1)).
Proof.
  intros n current Hcurrent.
  exists current, (current + 1). repeat split; try lia.
  left. repeat split.
  - rewrite prefix_parent_state_Znth__attainment by lia.
    destruct (Z_lt_dec current current); lia.
  - rewrite prefix_parent_state_Znth__attainment by lia.
    destruct (Z_lt_dec (current + 1) current); lia.
  - intros z Hz Hparent.
    rewrite prefix_parent_state_Znth__attainment in Hparent by lia.
    destruct (Z_lt_dec z current); lia.
  - symmetry. apply prefix_parent_state_step_replace__attainment.
    exact Hcurrent.
Qed.

Lemma prefix_parent_state_target__attainment : forall n,
  1 <= n -> TargetChain n (PrefixParentState n n).
Proof.
  intros n Hn. repeat split.
  - apply prefix_parent_state_length__attainment. lia.
  - intros x Hx. rewrite prefix_parent_state_Znth__attainment by lia.
    destruct (Z_lt_dec x n); lia.
  - rewrite prefix_parent_state_Znth__attainment by lia.
    destruct (Z_lt_dec n n); lia.
Qed.

Lemma prefix_parent_state_nesting_trace_nat__attainment :
  forall fuel n current,
    1 <= current ->
    n = current + Z.of_nat fuel ->
    exists states,
      MatryoshkaTrace n (PrefixParentState n current) states
        (PrefixParentState n n) /\
      Zlength states = Z.of_nat fuel + 1.
Proof.
  induction fuel as [|fuel IH]; intros n current Hcurrent Hn.
  - replace n with current by lia.
    exists [PrefixParentState current current]. split; [constructor|].
    rewrite Zlength_cons, Zlength_nil. lia.
  - assert (1 <= current + 1) by lia.
    assert (n = current + 1 + Z.of_nat fuel) as Hnext_n.
    { rewrite Nat2Z.inj_succ in Hn. lia. }
    destruct (IH n (current + 1) ltac:(lia) Hnext_n)
      as [states [Htrace Hlength]].
    exists (PrefixParentState n current :: states). split.
    + econstructor.
      * apply prefix_parent_state_nest_step__attainment.
        rewrite Nat2Z.inj_succ in Hn. split; lia.
      * exact Htrace.
    + rewrite Zlength_cons, Hlength, Nat2Z.inj_succ. lia.
Qed.

Lemma prefix_parent_state_nesting_phase__attainment : forall n kept,
  1 <= kept <= n ->
  exists states,
    MatryoshkaNestingPhase n kept
      (PrefixParentState n kept) (PrefixParentState n n) states.
Proof.
  intros n kept Hkept.
  destruct (prefix_parent_state_nesting_trace_nat__attainment
    (Z.to_nat (n - kept)) n kept ltac:(lia)) as [states [Htrace Hlength]].
  - rewrite Z2Nat.id by lia. lia.
  - exists states. unfold MatryoshkaNestingPhase.
    split; [exact Htrace|]. split.
    + rewrite Z2Nat.id in Hlength by lia. exact Hlength.
    + apply prefix_parent_state_target__attainment. lia.
Qed.

Lemma candidate_attainment_from_dismantling__attainment :
  forall n chains init dismantle_states,
    1 <= n ->
    Pre n chains ->
    MatryoshkaDismantlingPhase n chains (usable_prefix chains)
      init (PrefixParentState n (usable_prefix chains)) dismantle_states ->
    MatryoshkaAttainment n chains
      ((n - Zlength chains - (usable_prefix chains - 1)) +
       (n - usable_prefix chains)).
Proof.
  intros n chains init dismantle_states Hn Hpre Hdismantle.
  pose proof (usable_prefix_bounds__matryoshka_minimum
    n chains Hn Hpre) as Hkept.
  destruct (prefix_parent_state_nesting_phase__attainment
    n (usable_prefix chains) Hkept) as [nest_states Hnest].
  eapply matryoshka_phases_attainment__operational_architecture;
    [|exact Hdismantle|exact Hnest].
  apply pre_total_length__matryoshka_minimum; assumption.
Qed.

Lemma candidate_spec_from_dismantling__attainment :
  forall n chains init dismantle_states,
    1 <= n ->
    Pre n chains ->
    MatryoshkaDismantlingPhase n chains (usable_prefix chains)
      init (PrefixParentState n (usable_prefix chains)) dismantle_states ->
    Spec n chains
      ((n - Zlength chains - (usable_prefix chains - 1)) +
       (n - usable_prefix chains)).
Proof.
  intros n chains init dismantle_states Hn Hpre Hdismantle.
  assert (0 <=
    (n - Zlength chains - (usable_prefix chains - 1)) +
    (n - usable_prefix chains)) as Hmoves.
  { destruct Hdismantle as [Hparent [Htrace Hlength]].
    pose proof (matryoshka_trace_nonempty__operational_architecture
      n init dismantle_states
      (PrefixParentState n (usable_prefix chains)) Htrace) as Hnonempty.
    assert (0 < Zlength dismantle_states) as Hpositive_length.
    { destruct dismantle_states; [contradiction|].
      rewrite Zlength_cons. pose proof (Zlength_nonneg dismantle_states). lia. }
    pose proof (usable_prefix_bounds__matryoshka_minimum
      n chains Hn Hpre).
    pose proof (pre_total_length__matryoshka_minimum
      n chains Hn Hpre). lia. }
  eapply matryoshka_certificates_spec__operational_architecture.
  - exact Hmoves.
  - eapply candidate_attainment_from_dismantling__attainment; eauto.
  - apply matryoshka_candidate_lower_bound__input_edges; assumption.
Qed.

(** The input forest as an explicit, doll-indexed parent array.  Each row is
    converted to [(doll,next)] pairs, with [(outermost,0)] at its end. *)
Fixpoint RowParentPairs (row : list Z) : list (Z * Z) :=
  match row with
  | [] => []
  | doll :: rest =>
      match rest with
      | [] => [(doll, 0)]
      | parent :: _ => (doll, parent) :: RowParentPairs rest
      end
  end.

Definition InputParentPairs (chains : list (list Z)) : list (Z * Z) :=
  concat (map RowParentPairs chains).

Fixpoint ParentLookup (doll : Z) (pairs : list (Z * Z)) : Z :=
  match pairs with
  | [] => 0
  | (child, parent) :: rest =>
      if Z.eq_dec doll child then parent else ParentLookup doll rest
  end.

Definition CanonicalParentState (n : Z) (chains : list (list Z)) : list Z :=
  map (fun doll => ParentLookup doll (InputParentPairs chains))
    (Zrange 1 (n + 1)).

Lemma row_parent_pairs_keys__canonical_input : forall row,
  map fst (RowParentPairs row) = row.
Proof.
  induction row as [|doll rest IH]; [reflexivity|].
  destruct rest as [|parent tail]; simpl; [reflexivity|].
  f_equal. exact IH.
Qed.

Lemma input_parent_pairs_keys__canonical_input : forall chains,
  map fst (InputParentPairs chains) = concat chains.
Proof.
  induction chains as [|row rest IH]; simpl; [reflexivity|].
  unfold InputParentPairs in *. simpl.
  rewrite map_app, row_parent_pairs_keys__canonical_input, IH.
  reflexivity.
Qed.

Lemma parent_lookup_present__canonical_input : forall pairs child parent,
  NoDup (map fst pairs) ->
  In (child, parent) pairs ->
  ParentLookup child pairs = parent.
Proof.
  induction pairs as [|[head value] rest IH]; intros child parent Hnodup Hin;
    simpl in *; [contradiction|].
  inversion Hnodup as [|? ? Hhead Hrest]; subst.
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst. destruct (Z.eq_dec child child); congruence.
  - destruct (Z.eq_dec child head) as [Heq|Hneq].
    + subst head. exfalso. apply Hhead. apply in_map with (f := fst) in Hin.
      exact Hin.
    + apply IH; assumption.
Qed.

Lemma parent_lookup_zero_or_present__canonical_input : forall pairs child,
  ParentLookup child pairs = 0 \/
  In (child, ParentLookup child pairs) pairs.
Proof.
  induction pairs as [|[head value] rest IH]; intros child; simpl.
  - left. reflexivity.
  - destruct (Z.eq_dec child head) as [Heq|Hneq].
    + subst head. right. left. reflexivity.
    + destruct (IH child) as [Hzero|Hin].
      * left. exact Hzero.
      * right. right. exact Hin.
Qed.

Lemma row_parent_pairs_parent__canonical_input : forall row child parent,
  In (child, parent) (RowParentPairs row) ->
  parent = 0 \/ In parent row.
Proof.
  induction row as [|doll rest IH]; intros child parent Hin;
    simpl in Hin; [contradiction|].
  destruct rest as [|next tail]; simpl in Hin.
  - destruct Hin as [Hin|[]]. inversion Hin. left. reflexivity.
  - destruct Hin as [Hin|Hin].
    + inversion Hin; subst. right. simpl. auto.
    + destruct (IH child parent Hin) as [->|Hmember]; [left; reflexivity|].
      right. simpl. auto.
Qed.

Lemma input_parent_pairs_parent__canonical_input : forall chains child parent,
  In (child, parent) (InputParentPairs chains) ->
  parent = 0 \/ In parent (concat chains).
Proof.
  intros chains child parent Hin. unfold InputParentPairs in Hin.
  apply in_concat in Hin. destruct Hin as [pairs [Hpairs Hin]].
  apply in_map_iff in Hpairs.
  destruct Hpairs as [row [Hpairs Hrow]]. subst pairs.
  destruct (row_parent_pairs_parent__canonical_input row child parent Hin)
    as [->|Hmember]; [left; reflexivity|].
  right. apply in_concat. exists row. auto.
Qed.

Lemma row_parent_pairs_edge__canonical_input : forall row i,
  0 <= i < Zlength row - 1 ->
  In (Znth i row 0, Znth (i + 1) row 0) (RowParentPairs row).
Proof.
  induction row as [|doll rest IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct rest as [|parent tail].
    + rewrite Zlength_cons, Zlength_nil in Hi. lia.
    + destruct (Z.eq_dec i 0) as [->|Hne].
      * simpl. left. reflexivity.
      * assert (0 < i) by lia.
        change ((doll, parent) =
          (Znth i (doll :: parent :: tail) 0,
           Znth (i + 1) (doll :: parent :: tail) 0) \/
          In (Znth i (doll :: parent :: tail) 0,
              Znth (i + 1) (doll :: parent :: tail) 0)
             (RowParentPairs (parent :: tail))).
        right.
        assert (Znth i (doll :: parent :: tail) 0 =
          Znth (i - 1) (parent :: tail) 0) as Hfirst.
        { apply Znth_cons. lia. }
        assert (Znth (i + 1) (doll :: parent :: tail) 0 =
          Znth i (parent :: tail) 0) as Hsecond.
        { rewrite Znth_cons by lia. replace (i + 1 - 1) with i by lia.
          reflexivity. }
        rewrite Hfirst, Hsecond.
        pose proof (IH (i - 1) ltac:(rewrite Zlength_cons in Hi; lia)) as Hedge.
        replace (i - 1 + 1) with i in Hedge by lia. exact Hedge.
Qed.

Lemma row_parent_pairs_root__canonical_input : forall row,
  row <> [] ->
  In (Znth (Zlength row - 1) row 0, 0) (RowParentPairs row).
Proof.
  induction row as [|doll rest IH]; intros Hnonempty; [contradiction|].
  destruct rest as [|parent tail].
  - simpl. left. reflexivity.
  - change ((doll, parent) =
      (Znth (Zlength (doll :: parent :: tail) - 1)
        (doll :: parent :: tail) 0, 0) \/
      In (Znth (Zlength (doll :: parent :: tail) - 1)
        (doll :: parent :: tail) 0, 0)
        (RowParentPairs (parent :: tail))).
    right.
    assert (Znth (Zlength (doll :: parent :: tail) - 1)
      (doll :: parent :: tail) 0 =
      Znth (Zlength (parent :: tail) - 1) (parent :: tail) 0) as Hroot.
    { rewrite Zlength_cons.
      rewrite Znth_cons by
        (rewrite Zlength_cons; pose proof (Zlength_nonneg tail); lia).
      f_equal. lia. }
    rewrite Hroot. apply IH. discriminate.
Qed.

Lemma row_parent_pairs_in_input__canonical_input : forall chains row pair,
  In row chains -> In pair (RowParentPairs row) ->
  In pair (InputParentPairs chains).
Proof.
  intros chains row pair Hrow Hpair. unfold InputParentPairs.
  apply in_concat. exists (RowParentPairs row). split.
  - apply in_map. exact Hrow.
  - exact Hpair.
Qed.

Lemma canonical_parent_state_length__canonical_input : forall n chains,
  0 <= n -> Zlength (CanonicalParentState n chains) = n.
Proof.
  intros. unfold CanonicalParentState.
  rewrite Zlength_map__matryoshka_minimum.
  rewrite Zlength_Zrange__matryoshka_minimum by lia. lia.
Qed.

Lemma canonical_parent_state_Znth__canonical_input : forall n chains doll,
  0 <= n -> 1 <= doll <= n ->
  Znth (doll - 1) (CanonicalParentState n chains) 0 =
    ParentLookup doll (InputParentPairs chains).
Proof.
  intros n chains doll Hn Hdoll. unfold CanonicalParentState.
  rewrite (@Znth_map__input_edges Z Z
    (fun x => ParentLookup x (InputParentPairs chains))
    (Zrange 1 (n + 1)) 0 0 (doll - 1)) by
    (rewrite Zlength_Zrange__matryoshka_minimum by lia; lia).
  rewrite Znth_Zrange__input_edges by lia.
  replace (1 + (doll - 1)) with doll by lia. reflexivity.
Qed.

Lemma canonical_parent_state_chain_parent__canonical_input : forall n chains,
  1 <= n -> Pre n chains ->
  ChainParent n chains (CanonicalParentState n chains).
Proof.
  intros n chains Hn Hpre.
  destruct Hpre as [Hconcat [Hperm [Hnonempty Hmono]]].
  assert (NoDup (concat chains)) as Hnodup_concat.
  { eapply Permutation_NoDup; [symmetry; exact Hperm|apply NoDup_Zrange]. }
  assert (NoDup (map fst (InputParentPairs chains))) as Hnodup_pairs.
  { rewrite input_parent_pairs_keys__canonical_input. exact Hnodup_concat. }
  split.
  - apply canonical_parent_state_length__canonical_input. lia.
  - split.
    + intros x Hx. rewrite canonical_parent_state_Znth__canonical_input by lia.
      destruct (parent_lookup_zero_or_present__canonical_input
        (InputParentPairs chains) x) as [Hzero|Hin].
      * left. exact Hzero.
      * destruct (input_parent_pairs_parent__canonical_input
          chains x _ Hin) as [Hzero|Hmember].
        -- left. exact Hzero.
        -- right. apply (Permutation_in _ Hperm) in Hmember.
           rewrite <- In_Zrange in Hmember. lia.
    + intros row Hrow. split.
      * intros i Hi.
      pose proof (row_parent_pairs_edge__canonical_input row i Hi) as Hedge.
      pose proof (row_parent_pairs_in_input__canonical_input
        chains row _ Hrow Hedge) as Hin.
      pose proof (pre_row_value_bounds__input_profile n chains row
        (Znth i row 0) ltac:(repeat split; assumption) Hrow
        (Znth_In_Zlength row 0 i ltac:(lia))) as Hchild.
      rewrite canonical_parent_state_Znth__canonical_input by lia.
      eapply parent_lookup_present__canonical_input; eauto.
      * assert (row <> []) as Hrow_nonempty.
        { exact ((proj1 (@Forall_forall (list Z)
            (fun ch => ch <> []) chains)) Hnonempty row Hrow). }
      pose proof (row_parent_pairs_root__canonical_input row Hrow_nonempty) as Hroot.
      pose proof (row_parent_pairs_in_input__canonical_input
        chains row _ Hrow Hroot) as Hin.
      pose proof (pre_row_value_bounds__input_profile n chains row
        (Znth (Zlength row - 1) row 0) ltac:(repeat split; assumption) Hrow
        (Znth_In_Zlength row 0 (Zlength row - 1)
          ltac:(destruct row; [contradiction|];
          rewrite Zlength_cons; pose proof (Zlength_nonneg row); lia))) as Hchild.
      rewrite canonical_parent_state_Znth__canonical_input by lia.
      eapply parent_lookup_present__canonical_input; eauto.
Qed.

(** A deterministic dismantling schedule.  A row is traversed from its outer
    end toward its inner end; roots and the retained [1..kept] adjacencies are
    omitted.  The accumulated source list gives the state after each prefix
    of that schedule without hiding any update behind an existential. *)
Definition IsScheduledRemoval (kept : Z) (edge : Z * Z) : bool :=
  if Z.eq_dec (snd edge) 0 then false
  else if Z_le_dec kept (fst edge) then true else false.

Definition RowDismantlingOrder (kept : Z) (row : list Z) : list (Z * Z) :=
  filter (IsScheduledRemoval kept) (rev (RowParentPairs row)).

Definition DismantlingOrder
    (kept : Z) (chains : list (list Z)) : list (Z * Z) :=
  concat (map (RowDismantlingOrder kept) chains).

Definition ClearedParentState
    (n : Z) (chains : list (list Z)) (removed : list Z) : list Z :=
  map (fun doll =>
    if in_dec Z.eq_dec doll removed then 0
    else ParentLookup doll (InputParentPairs chains))
    (Zrange 1 (n + 1)).

Fixpoint DismantlingStatesFrom
    (n : Z) (chains : list (list Z))
    (removed : list Z) (order : list (Z * Z)) : list (list Z) :=
  ClearedParentState n chains removed ::
  match order with
  | [] => []
  | (child, _) :: rest =>
      DismantlingStatesFrom n chains (child :: removed) rest
  end.

Definition CanonicalDismantlingStates
    (n kept : Z) (chains : list (list Z)) : list (list Z) :=
  DismantlingStatesFrom n chains [] (DismantlingOrder kept chains).

Lemma cleared_parent_state_none__dismantling_schedule : forall n chains,
  ClearedParentState n chains [] = CanonicalParentState n chains.
Proof.
  intros n chains. unfold ClearedParentState, CanonicalParentState.
  apply map_ext. intros doll. simpl. reflexivity.
Qed.

Lemma cleared_parent_state_length__dismantling_schedule :
  forall n chains removed,
    0 <= n -> Zlength (ClearedParentState n chains removed) = n.
Proof.
  intros. unfold ClearedParentState.
  rewrite Zlength_map__matryoshka_minimum.
  rewrite Zlength_Zrange__matryoshka_minimum by lia. lia.
Qed.

Lemma cleared_parent_state_Znth__dismantling_schedule :
  forall n chains removed doll,
    0 <= n -> 1 <= doll <= n ->
    Znth (doll - 1) (ClearedParentState n chains removed) 0 =
      if in_dec Z.eq_dec doll removed then 0
      else ParentLookup doll (InputParentPairs chains).
Proof.
  intros n chains removed doll Hn Hdoll. unfold ClearedParentState.
  rewrite (@Znth_map__input_edges Z Z
    (fun x => if in_dec Z.eq_dec x removed then 0
      else ParentLookup x (InputParentPairs chains))
    (Zrange 1 (n + 1)) 0 0 (doll - 1)) by
    (rewrite Zlength_Zrange__matryoshka_minimum by lia; lia).
  rewrite Znth_Zrange__input_edges by lia.
  replace (1 + (doll - 1)) with doll by lia. reflexivity.
Qed.

Lemma dismantling_states_from_length__dismantling_schedule :
  forall n chains removed order,
    Zlength (DismantlingStatesFrom n chains removed order) =
      Z.of_nat (length order) + 1.
Proof.
  intros n chains removed order. revert removed.
  induction order as [|[child parent] rest IH]; intros removed; simpl.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - rewrite Zlength_cons, IH. lia.
Qed.

Lemma canonical_dismantling_states_start__dismantling_schedule :
  forall n kept chains,
    Znth 0 (CanonicalDismantlingStates n kept chains) [] =
      CanonicalParentState n chains.
Proof.
  intros. unfold CanonicalDismantlingStates.
  destruct (DismantlingOrder kept chains) as [|[child parent] rest]; simpl;
    apply cleared_parent_state_none__dismantling_schedule.
Qed.

Lemma canonical_dismantling_states_length__dismantling_schedule :
  forall n kept chains,
    Zlength (CanonicalDismantlingStates n kept chains) =
      Z.of_nat (length (DismantlingOrder kept chains)) + 1.
Proof.
  intros. unfold CanonicalDismantlingStates.
  apply dismantling_states_from_length__dismantling_schedule.
Qed.

Lemma cleared_parent_state_step_replace__dismantling_schedule :
  forall n chains removed child,
    1 <= child <= n ->
    replace_Znth (child - 1) 0 (ClearedParentState n chains removed) =
      ClearedParentState n chains (child :: removed).
Proof.
  intros n chains removed child Hchild.
  apply nth_ext with (d := 0) (d' := 0).
  - apply Nat2Z.inj. rewrite <- !Zlength_correct.
    rewrite Zlength_replace_Znth__deficit_measure.
    rewrite !cleared_parent_state_length__dismantling_schedule by lia.
    reflexivity.
  - intros index Hindex.
    assert (0 <= Z.of_nat index < n) as Hi.
    { assert (Z.of_nat index < Zlength
        (replace_Znth (child - 1) 0
          (ClearedParentState n chains removed))) as HindexZ.
      { rewrite Zlength_correct. lia. }
      rewrite Zlength_replace_Znth__deficit_measure,
        cleared_parent_state_length__dismantling_schedule in HindexZ by lia.
      lia. }
    assert (Znth (Z.of_nat index)
      (replace_Znth (child - 1) 0
        (ClearedParentState n chains removed)) 0 =
      Znth (Z.of_nat index)
        (ClearedParentState n chains (child :: removed)) 0) as Heq.
    { destruct (Z.eq_dec (Z.of_nat index) (child - 1)) as [Heqi|Hneq].
      - rewrite Heqi.
        rewrite Znth_replace_Znth_Same by
          (rewrite cleared_parent_state_length__dismantling_schedule by lia; lia).
        rewrite (cleared_parent_state_Znth__dismantling_schedule
          n chains (child :: removed) child) by lia.
        destruct (in_dec Z.eq_dec child (child :: removed)); [reflexivity|].
        exfalso. apply n0. left. reflexivity.
      - rewrite Znth_replace_Znth_Diff by
          (try rewrite cleared_parent_state_length__dismantling_schedule by lia; lia).
        replace (Z.of_nat index) with (Z.of_nat index + 1 - 1) by lia.
        rewrite (cleared_parent_state_Znth__dismantling_schedule
          n chains removed (Z.of_nat index + 1)) by lia.
        rewrite (cleared_parent_state_Znth__dismantling_schedule
          n chains (child :: removed) (Z.of_nat index + 1)) by lia.
        destruct (in_dec Z.eq_dec (Z.of_nat index + 1) removed) as [Hin|Hnotin].
        + destruct (in_dec Z.eq_dec (Z.of_nat index + 1)
            (child :: removed)) as [Hincons|Hnotcons]; [reflexivity|].
          exfalso. apply Hnotcons. right. exact Hin.
        + destruct (in_dec Z.eq_dec (Z.of_nat index + 1)
            (child :: removed)) as [Hincons|Hnotcons].
          * destruct Hincons as [Heqchild|Hinremoved]; [lia|].
            exfalso. apply Hnotin. exact Hinremoved.
          * reflexivity. }
    unfold Znth in Heq. rewrite !Nat2Z.id in Heq. exact Heq.
Qed.

Lemma cleared_parent_state_remove_step__dismantling_schedule :
  forall n chains removed child parent,
    1 <= child <= n -> 1 <= parent <= n -> child <> parent ->
    ~ In child removed ->
    ParentLookup child (InputParentPairs chains) = parent ->
    Znth (parent - 1) (ClearedParentState n chains removed) 0 = 0 ->
    NestStep n (ClearedParentState n chains removed)
      (ClearedParentState n chains (child :: removed)).
Proof.
  intros n chains removed child parent Hchild Hparent Hneq
    Hfresh Hlookup Hroot.
  exists child, parent. repeat split; try lia.
  right. repeat split.
  - rewrite cleared_parent_state_Znth__dismantling_schedule by lia.
    destruct (in_dec Z.eq_dec child removed); [contradiction|exact Hlookup].
  - exact Hroot.
  - symmetry. apply cleared_parent_state_step_replace__dismantling_schedule.
    exact Hchild.
Qed.

Lemma dismantling_order_in_input__dismantling_schedule :
  forall kept chains edge,
    In edge (DismantlingOrder kept chains) ->
    In edge (InputParentPairs chains) /\
    snd edge <> 0 /\ kept <= fst edge.
Proof.
  intros kept chains edge Hin. unfold DismantlingOrder in Hin.
  apply in_concat in Hin. destruct Hin as [ordered [Hordered Hedge]].
  apply in_map_iff in Hordered.
  destruct Hordered as [row [Hordered Hrow]]. subst ordered.
  unfold RowDismantlingOrder in Hedge.
  apply filter_In in Hedge. destruct Hedge as [Hedge Hscheduled].
  apply in_rev in Hedge. split.
  - apply row_parent_pairs_in_input__canonical_input with (row := row);
      assumption.
  - unfold IsScheduledRemoval in Hscheduled.
    destruct (Z.eq_dec (snd edge) 0) as [Hzero|Hnonzero];
      [discriminate|].
    destruct (Z_le_dec kept (fst edge)) as [Hle|Hnle];
      [split; assumption|discriminate].
Qed.

Lemma row_parent_pairs_distinct__dismantling_schedule :
  forall row child parent,
    mono_inc row ->
    In (child, parent) (RowParentPairs row) ->
    parent <> 0 -> child <> parent.
Proof.
  induction row as [|doll rest IH]; intros child parent Hmono Hedge Hnonzero;
    simpl in Hedge; [contradiction|].
  destruct rest as [|next tail]; simpl in Hedge.
  - destruct Hedge as [Hedge|[]]. inversion Hedge; subst.
    exfalso. apply Hnonzero. reflexivity.
  - destruct Hedge as [Hedge|Hedge].
    + inversion Hedge; subst.
      assert (1 < Zlength (child :: parent :: tail)) as Hlen.
      { rewrite !Zlength_cons. pose proof (Zlength_nonneg tail). lia. }
      pose proof (Hmono 0 1 ltac:(lia) ltac:(lia) Hlen) as Hlt.
      change (child < parent) in Hlt. lia.
    + eapply IH; eauto.
      exact (proj2 (proj1 (mono_inc_cons doll (next :: tail)) Hmono)).
Qed.

Lemma dismantling_order_edge_profile__dismantling_schedule :
  forall n kept chains child parent,
    1 <= n -> Pre n chains ->
    In (child, parent) (DismantlingOrder kept chains) ->
    1 <= child <= n /\ 1 <= parent <= n /\ child <> parent /\
    kept <= child /\
    ParentLookup child (InputParentPairs chains) = parent.
Proof.
  intros n kept chains child parent Hn Hpre Hin.
  pose proof (dismantling_order_in_input__dismantling_schedule
    kept chains (child, parent) Hin) as [Hinput [Hparent_nonzero Hkept]].
  assert (In child (concat chains)) as Hchild_in.
  { rewrite <- input_parent_pairs_keys__canonical_input.
    apply in_map with (f := fst) in Hinput. exact Hinput. }
  destruct (input_parent_pairs_parent__canonical_input
    chains child parent Hinput) as [Hzero|Hparent_in]; [contradiction|].
  pose proof (pre_concat_value_bounds__input_profile
    n chains child Hpre Hchild_in) as Hchild.
  pose proof (pre_concat_value_bounds__input_profile
    n chains parent Hpre Hparent_in) as Hparent.
  assert (NoDup (map fst (InputParentPairs chains))) as Hnodup.
  { rewrite input_parent_pairs_keys__canonical_input.
    destruct Hpre as [_ [Hperm _]].
    eapply Permutation_NoDup; [symmetry; exact Hperm|apply NoDup_Zrange]. }
  split; [exact Hchild|]. split; [exact Hparent|]. split.
  - destruct Hpre as [_ [_ [_ Hallmono]]].
    apply in_concat in Hinput.
    destruct Hinput as [pairs [Hpairs Hedge]].
    apply in_map_iff in Hpairs.
    destruct Hpairs as [row [Hpairs Hrow]]. subst pairs.
    pose proof ((proj1 (@Forall_forall (list Z) mono_inc chains))
      Hallmono row Hrow) as Hrowmono.
    eapply row_parent_pairs_distinct__dismantling_schedule; eauto.
  - split; [exact Hkept|].
    eapply parent_lookup_present__canonical_input; eauto.
Qed.

(** One global fold invariant for a removal schedule.  Besides recording the
    local edge profile, it records exactly the two prefix facts needed by a
    legal removal: the source is fresh and the target is already a root. *)
Inductive RemovalScheduleReady
    (n : Z) (chains : list (list Z)) :
    list Z -> list (Z * Z) -> Prop :=
| RemovalScheduleReady_nil : forall removed,
    RemovalScheduleReady n chains removed []
| RemovalScheduleReady_cons : forall removed child parent rest,
    1 <= child <= n ->
    1 <= parent <= n ->
    child <> parent ->
    ~ In child removed ->
    ParentLookup child (InputParentPairs chains) = parent ->
    (In parent removed \/
      ParentLookup parent (InputParentPairs chains) = 0) ->
    RemovalScheduleReady n chains (child :: removed) rest ->
    RemovalScheduleReady n chains removed ((child, parent) :: rest).

Definition RemovedAfter
    (removed : list Z) (order : list (Z * Z)) : list Z :=
  rev (map fst order) ++ removed.

Lemma removed_after_cons__global_schedule : forall removed child parent rest,
  RemovedAfter removed ((child, parent) :: rest) =
    RemovedAfter (child :: removed) rest.
Proof.
  intros. unfold RemovedAfter. simpl. rewrite <- app_assoc. reflexivity.
Qed.

Lemma removal_schedule_ready_trace__global_schedule :
  forall n chains removed order,
    RemovalScheduleReady n chains removed order ->
    MatryoshkaTrace n (ClearedParentState n chains removed)
      (DismantlingStatesFrom n chains removed order)
      (ClearedParentState n chains (RemovedAfter removed order)).
Proof.
  intros n chains removed order Hready.
  induction Hready as [removed|
    removed child parent rest Hchild Hparent Hneq Hfresh Hlookup
    Hroot Hready IH].
  - simpl. unfold RemovedAfter. simpl. constructor.
  - simpl. econstructor.
    + eapply cleared_parent_state_remove_step__dismantling_schedule
        with (parent := parent).
      * exact Hchild.
      * exact Hparent.
      * exact Hneq.
      * exact Hfresh.
      * exact Hlookup.
      * rewrite cleared_parent_state_Znth__dismantling_schedule by lia.
        destruct (in_dec Z.eq_dec parent removed) as [Hin|Hnotin].
        -- reflexivity.
        -- destruct Hroot as [Hin|Hparent_lookup];
             [contradiction|exact Hparent_lookup].
    + rewrite removed_after_cons__global_schedule. exact IH.
Qed.

Lemma removal_schedule_ready_sources_fresh__global_schedule :
  forall n chains removed order,
    RemovalScheduleReady n chains removed order ->
    NoDup removed ->
    NoDup (RemovedAfter removed order).
Proof.
  intros n chains removed order Hready. induction Hready; intros Hnodup.
  - unfold RemovedAfter. simpl. exact Hnodup.
  - rewrite removed_after_cons__global_schedule.
    apply IHHready. constructor; assumption.
Qed.

Lemma removal_schedule_ready_app__global_schedule :
  forall n chains removed left right,
    RemovalScheduleReady n chains removed left ->
    RemovalScheduleReady n chains (RemovedAfter removed left) right ->
    RemovalScheduleReady n chains removed (left ++ right).
Proof.
  intros n chains removed left right Hleft. revert right.
  induction Hleft as [removed|
    removed child parent rest Hchild Hparent Hneq Hfresh Hlookup
    Hroot Hrest IH]; intros right Hright.
  - simpl in *. exact Hright.
  - simpl. eapply RemovalScheduleReady_cons with (parent := parent);
      try eassumption.
    apply IH.
    rewrite <- (removed_after_cons__global_schedule
      removed child parent rest). exact Hright.
Qed.

Lemma row_dismantling_order_cons__global_schedule :
  forall kept child parent tail,
    parent <> 0 ->
    RowDismantlingOrder kept (child :: parent :: tail) =
      RowDismantlingOrder kept (parent :: tail) ++
      if Z_le_dec kept child then [(child, parent)] else [].
Proof.
  intros kept child parent tail Hparent.
  unfold RowDismantlingOrder. simpl.
  rewrite filter_app. simpl. unfold IsScheduledRemoval. simpl.
  destruct (Z.eq_dec parent 0); [contradiction|].
  destruct (Z_le_dec kept child); reflexivity.
Qed.

Lemma row_dismantling_order_in_pairs__global_schedule :
  forall kept row edge,
    In edge (RowDismantlingOrder kept row) ->
    In edge (RowParentPairs row).
Proof.
  intros kept row edge Hin. unfold RowDismantlingOrder in Hin.
  apply filter_In in Hin. destruct Hin as [Hin _].
  apply in_rev in Hin. exact Hin.
Qed.

Lemma row_dismantling_order_source_in_row__global_schedule :
  forall kept row source parent,
    In (source, parent) (RowDismantlingOrder kept row) ->
    In source row.
Proof.
  intros kept row source parent Hin.
  pose proof (row_dismantling_order_in_pairs__global_schedule
    kept row (source, parent) Hin) as Hpairs.
  rewrite <- row_parent_pairs_keys__canonical_input.
  apply in_map with (f := fst) in Hpairs. exact Hpairs.
Qed.

Lemma row_dismantling_order_contains_head__global_schedule :
  forall kept child parent tail,
    parent <> 0 -> kept <= child ->
    In child (map fst (RowDismantlingOrder kept (child :: parent :: tail))).
Proof.
  intros kept child parent tail Hparent Hkept.
  rewrite row_dismantling_order_cons__global_schedule by assumption.
  destruct (Z_le_dec kept child); [|lia].
  rewrite map_app. apply in_or_app. right. simpl. auto.
Qed.

Lemma row_dismantling_ready_aux__global_schedule :
  forall n chains kept row removed,
    (forall value, In value row -> 1 <= value <= n) ->
    mono_inc row ->
    NoDup row ->
    NoDup (map fst (InputParentPairs chains)) ->
    (forall edge, In edge (RowParentPairs row) ->
      In edge (InputParentPairs chains)) ->
    (forall value, In value row -> ~ In value removed) ->
    RemovalScheduleReady n chains removed
      (RowDismantlingOrder kept row).
Proof.
  intros n chains kept row. induction row as [|child rest IH]; intros removed
    Hbounds Hmono Hnodup Hinput_nodup Hpairs Hdisjoint.
  - unfold RowDismantlingOrder. simpl. constructor.
  - destruct rest as [|parent tail].
    + unfold RowDismantlingOrder. simpl. unfold IsScheduledRemoval. simpl.
      destruct (Z.eq_dec 0 0); [constructor|contradiction].
    + assert (1 <= child <= n) as Hchild by
        (apply Hbounds; simpl; auto).
      assert (1 <= parent <= n) as Hparent by
        (apply Hbounds; simpl; auto).
      assert (parent <> 0) as Hparent_nonzero by lia.
      rewrite row_dismantling_order_cons__global_schedule by exact Hparent_nonzero.
      assert (RemovalScheduleReady n chains removed
        (RowDismantlingOrder kept (parent :: tail))) as Htail_ready.
      { apply IH.
        - intros value Hin. apply Hbounds. right. exact Hin.
        - exact (proj2 (proj1
            (mono_inc_cons child (parent :: tail)) Hmono)).
        - inversion Hnodup. assumption.
        - exact Hinput_nodup.
        - intros edge Hedge. apply Hpairs. simpl. right. exact Hedge.
        - intros value Hin. apply Hdisjoint. right. exact Hin. }
      destruct (Z_le_dec kept child) as [Hkept|Hnotkept].
      * eapply removal_schedule_ready_app__global_schedule.
        -- exact Htail_ready.
        -- eapply RemovalScheduleReady_cons with (parent := parent).
           ++ exact Hchild.
           ++ exact Hparent.
           ++ pose proof (Hmono 0 1 ltac:(lia) ltac:(lia)
                ltac:(rewrite !Zlength_cons;
                  pose proof (Zlength_nonneg tail); lia)) as Hlt.
              change (child < parent) in Hlt. lia.
           ++ unfold RemovedAfter. intro Hin.
              apply in_app_or in Hin. destruct Hin as [Hsource|Hremoved].
              ** apply in_rev in Hsource.
                 apply in_map_iff in Hsource.
                 destruct Hsource as [[source target] [Hsource Hedge]].
                 simpl in Hsource. subst source.
                 pose proof (row_dismantling_order_source_in_row__global_schedule
                   kept (parent :: tail) child target Hedge) as Hin_tail.
                 inversion Hnodup. contradiction.
              ** apply (Hdisjoint child ltac:(simpl; auto)). exact Hremoved.
           ++ apply parent_lookup_present__canonical_input; [exact Hinput_nodup|].
              apply Hpairs. simpl. left. reflexivity.
           ++ destruct tail as [|outer more].
              ** right. apply parent_lookup_present__canonical_input;
                   [exact Hinput_nodup|].
                 apply Hpairs. simpl. right. simpl. left. reflexivity.
              ** left. unfold RemovedAfter. apply in_or_app. left.
                 apply (proj1 (in_rev _ parent)).
                 apply row_dismantling_order_contains_head__global_schedule.
                 --- assert (1 <= outer <= n) as Houter by
                       (apply Hbounds; simpl; auto). lia.
                 --- assert (1 < Zlength (child :: parent :: outer :: more))
                       as Hlen.
                     { rewrite !Zlength_cons.
                       pose proof (Zlength_nonneg more). lia. }
                     pose proof (Hmono 0 1 ltac:(lia) ltac:(lia) Hlen) as Hlt.
                     change (child < parent) in Hlt. lia.
           ++ constructor.
      * rewrite app_nil_r. exact Htail_ready.
Qed.

Lemma nodup_app_disjoint__global_schedule : forall (left right : list Z),
  NoDup (left ++ right) ->
  forall value, In value left -> ~ In value right.
Proof.
  induction left as [|head tail IH]; intros right Hnodup value Hin;
    simpl in *; [contradiction|].
  inversion Hnodup as [|? ? Hhead Htail]; subst.
  destruct Hin as [->|Hin].
  - intro Hright. apply Hhead. apply in_or_app. right. exact Hright.
  - eapply IH; eauto.
Qed.

Lemma dismantling_order_ready_aux__global_schedule :
  forall n full_chains kept rows removed,
    (forall value, In value (concat rows) -> 1 <= value <= n) ->
    Forall mono_inc rows ->
    NoDup (concat rows) ->
    NoDup (map fst (InputParentPairs full_chains)) ->
    (forall row edge, In row rows -> In edge (RowParentPairs row) ->
      In edge (InputParentPairs full_chains)) ->
    (forall value, In value (concat rows) -> ~ In value removed) ->
    RemovalScheduleReady n full_chains removed
      (DismantlingOrder kept rows).
Proof.
  intros n full_chains kept rows. induction rows as [|row rest IH];
    intros removed Hbounds Hmono Hnodup Hinput_nodup Hpairs Hdisjoint.
  - unfold DismantlingOrder. simpl. constructor.
  - unfold DismantlingOrder. simpl.
    change (RemovalScheduleReady n full_chains removed
      (RowDismantlingOrder kept row ++ DismantlingOrder kept rest)).
    assert (NoDup row) as Hrow_nodup.
    { eapply NoDup_app_remove_r; eauto. }
    assert (NoDup (concat rest)) as Hrest_nodup.
    { eapply NoDup_app_remove_l; eauto. }
    pose proof (nodup_app_disjoint__global_schedule
      row (concat rest) Hnodup) as Hcross.
    inversion Hmono as [|? ? Hrow_mono Hrest_mono]; subst.
    assert (RemovalScheduleReady n full_chains removed
      (RowDismantlingOrder kept row)) as Hrow_ready.
    { apply row_dismantling_ready_aux__global_schedule.
      - intros value Hin. apply Hbounds. apply in_or_app. left. exact Hin.
      - exact Hrow_mono.
      - exact Hrow_nodup.
      - exact Hinput_nodup.
      - intros edge Hedge. apply Hpairs with (row := row); [left; reflexivity|assumption].
      - intros value Hin. apply Hdisjoint. apply in_or_app. left. exact Hin. }
    eapply removal_schedule_ready_app__global_schedule.
    + exact Hrow_ready.
    + change (RemovalScheduleReady n full_chains
        (RemovedAfter removed (RowDismantlingOrder kept row))
        (DismantlingOrder kept rest)).
      apply (IH (RemovedAfter removed (RowDismantlingOrder kept row))).
      * intros value Hin. apply Hbounds. apply in_or_app. right. exact Hin.
      * exact Hrest_mono.
      * exact Hrest_nodup.
      * exact Hinput_nodup.
      * intros other edge Hother Hedge.
        apply Hpairs with (row := other); [right; exact Hother|exact Hedge].
      * intros value Hin Hremoved.
        unfold RemovedAfter in Hremoved.
        apply in_app_or in Hremoved. destruct Hremoved as [Hsource|Hremoved].
        -- apply (proj2 (in_rev _ value)) in Hsource.
          apply in_map_iff in Hsource.
          destruct Hsource as [[source parent] [Hsource Hedge]].
          simpl in Hsource. subst source.
          pose proof (row_dismantling_order_source_in_row__global_schedule
            kept row value parent Hedge) as Hrow_value.
          eapply Hcross; eauto.
        -- apply (Hdisjoint value).
           ++ apply in_or_app. right. exact Hin.
           ++ exact Hremoved.
Qed.

Lemma dismantling_order_ready__global_schedule : forall n chains kept,
  1 <= n -> Pre n chains ->
  RemovalScheduleReady n chains [] (DismantlingOrder kept chains).
Proof.
  intros n chains kept Hn Hpre.
  assert (NoDup (concat chains)) as Hconcat_nodup.
  { destruct Hpre as [_ [Hperm _]].
    eapply Permutation_NoDup; [symmetry; exact Hperm|apply NoDup_Zrange]. }
  assert (NoDup (map fst (InputParentPairs chains))) as Hinput_nodup.
  { rewrite input_parent_pairs_keys__canonical_input. exact Hconcat_nodup. }
  apply dismantling_order_ready_aux__global_schedule.
  - intros value Hin. eapply pre_concat_value_bounds__input_profile; eauto.
  - destruct Hpre as [_ [_ [_ Hmono]]]. exact Hmono.
  - exact Hconcat_nodup.
  - exact Hinput_nodup.
  - intros row edge Hrow Hedge.
    eapply row_parent_pairs_in_input__canonical_input; eauto.
  - intros value Hin Hempty. contradiction.
Qed.

Lemma canonical_dismantling_trace__global_schedule : forall n chains kept,
  1 <= n -> Pre n chains ->
  MatryoshkaTrace n (CanonicalParentState n chains)
    (CanonicalDismantlingStates n kept chains)
    (ClearedParentState n chains
      (RemovedAfter [] (DismantlingOrder kept chains))).
Proof.
  intros n chains kept Hn Hpre.
  unfold CanonicalDismantlingStates.
  rewrite <- cleared_parent_state_none__dismantling_schedule.
  apply removal_schedule_ready_trace__global_schedule.
  apply dismantling_order_ready__global_schedule; assumption.
Qed.

Lemma dismantling_order_complete__global_schedule :
  forall kept chains child parent,
    In (child, parent) (InputParentPairs chains) ->
    parent <> 0 -> kept <= child ->
    In (child, parent) (DismantlingOrder kept chains).
Proof.
  intros kept chains child parent Hinput Hparent Hkept.
  unfold InputParentPairs in Hinput.
  apply in_concat in Hinput. destruct Hinput as [pairs [Hpairs Hedge]].
  apply in_map_iff in Hpairs.
  destruct Hpairs as [row [Hpairs Hrow]]. subst pairs.
  unfold DismantlingOrder. apply in_concat.
  exists (RowDismantlingOrder kept row). split.
  - apply in_map. exact Hrow.
  - unfold RowDismantlingOrder. apply filter_In. split.
    + apply (proj1 (in_rev _ (child, parent))). exact Hedge.
    + unfold IsScheduledRemoval. simpl.
      destruct (Z.eq_dec parent 0); [contradiction|].
      destruct (Z_le_dec kept child); [reflexivity|lia].
Qed.

Lemma dismantling_removed_source_characterization__global_schedule :
  forall kept chains child,
    In child (RemovedAfter [] (DismantlingOrder kept chains)) <->
    exists parent,
      In (child, parent) (InputParentPairs chains) /\
      parent <> 0 /\ kept <= child.
Proof.
  intros kept chains child. unfold RemovedAfter. rewrite app_nil_r.
  rewrite <- in_rev. split.
  - intros Hin. apply in_map_iff in Hin.
    destruct Hin as [[source parent] [Hsource Hedge]].
    simpl in Hsource. subst source. exists parent.
    pose proof (dismantling_order_in_input__dismantling_schedule
      kept chains (child, parent) Hedge) as [Hinput [Hnonzero Hkept]].
    auto.
  - intros [parent [Hinput [Hnonzero Hkept]]].
    apply in_map_iff. exists (child, parent). split; [reflexivity|].
    eapply dismantling_order_complete__global_schedule; eauto.
Qed.

Lemma canonical_parent_state_usable_prefix__global_schedule :
  forall n chains,
    1 <= n -> Pre n chains ->
    ConsecutivePrefix (usable_prefix chains)
      (CanonicalParentState n chains).
Proof.
  intros n chains Hn Hpre x Hx.
  pose proof (usable_prefix_characterization__matryoshka_minimum
    n chains Hn Hpre) as [Hcandidate _].
  destruct Hcandidate as [Hone|[row [Hrow [[Hq Hrowlen] Hvalues]]]].
  - lia.
  - pose proof (canonical_parent_state_chain_parent__canonical_input
      n chains Hn Hpre) as [_ [_ Hchains]].
    specialize (Hchains row Hrow) as [Hinternal Hroot].
    specialize (Hinternal (x - 1) ltac:(lia)).
    rewrite (Hvalues (x - 1)) in Hinternal by lia.
    replace (x - 1 + 1) with x in Hinternal by lia.
    rewrite (Hvalues x) in Hinternal by lia.
    exact Hinternal.
Qed.

Lemma canonical_dismantling_endpoint__global_schedule : forall n chains,
  1 <= n -> Pre n chains ->
  ClearedParentState n chains
    (RemovedAfter [] (DismantlingOrder (usable_prefix chains) chains)) =
  PrefixParentState n (usable_prefix chains).
Proof.
  intros n chains Hn Hpre.
  pose proof (usable_prefix_bounds__matryoshka_minimum
    n chains Hn Hpre) as Hkept.
  pose proof (canonical_parent_state_usable_prefix__global_schedule
    n chains Hn Hpre) as Hprefix.
  apply nth_ext with (d := 0) (d' := 0).
  - apply Nat2Z.inj. rewrite <- !Zlength_correct.
    rewrite cleared_parent_state_length__dismantling_schedule by lia.
    rewrite prefix_parent_state_length__attainment by lia. reflexivity.
  - intros index Hindex.
    assert (0 <= Z.of_nat index < n) as Hi.
    { assert (Z.of_nat index < Zlength
        (ClearedParentState n chains
          (RemovedAfter []
            (DismantlingOrder (usable_prefix chains) chains)))) as HindexZ.
      { rewrite Zlength_correct. lia. }
      rewrite cleared_parent_state_length__dismantling_schedule in HindexZ by lia.
      lia. }
    set (doll := Z.of_nat index + 1).
    assert (1 <= doll <= n) as Hdoll by (unfold doll; lia).
    assert (Znth (doll - 1)
      (ClearedParentState n chains
        (RemovedAfter []
          (DismantlingOrder (usable_prefix chains) chains))) 0 =
      Znth (doll - 1)
        (PrefixParentState n (usable_prefix chains)) 0) as Heq.
    { rewrite cleared_parent_state_Znth__dismantling_schedule by lia.
      rewrite prefix_parent_state_Znth__attainment by lia.
      destruct (Z_lt_dec doll (usable_prefix chains)) as [Hdoll_kept|Hdoll_notkept].
      - destruct (in_dec Z.eq_dec doll
          (RemovedAfter []
            (DismantlingOrder (usable_prefix chains) chains))) as [Hin|Hnotin].
        + rewrite dismantling_removed_source_characterization__global_schedule
            in Hin.
          destruct Hin as [parent [_ [_ Hsource]]]. lia.
        + pose proof (Hprefix doll ltac:(lia)) as Hcanonical.
          rewrite canonical_parent_state_Znth__canonical_input in Hcanonical by lia.
          exact Hcanonical.
      - destruct (Z.eq_dec
          (ParentLookup doll (InputParentPairs chains)) 0) as [Hzero|Hnonzero].
        + rewrite Hzero. destruct (in_dec Z.eq_dec doll
            (RemovedAfter []
              (DismantlingOrder (usable_prefix chains) chains)));
            destruct (Z_lt_dec doll (usable_prefix chains)); try lia; reflexivity.
        + destruct (parent_lookup_zero_or_present__canonical_input
            (InputParentPairs chains) doll) as [Hzero|Hinpair];
            [contradiction|].
          assert (In doll (RemovedAfter []
            (DismantlingOrder (usable_prefix chains) chains))) as Hin.
          { rewrite dismantling_removed_source_characterization__global_schedule.
            exists (ParentLookup doll (InputParentPairs chains)).
            repeat split; try assumption; lia. }
          destruct (in_dec Z.eq_dec doll
            (RemovedAfter []
              (DismantlingOrder (usable_prefix chains) chains)));
            [|contradiction].
          destruct (Z_lt_dec doll (usable_prefix chains)); try lia; reflexivity. }
    unfold doll in Heq. replace (Z.of_nat index + 1 - 1)
      with (Z.of_nat index) in Heq by lia.
    unfold Znth in Heq. rewrite !Nat2Z.id in Heq. exact Heq.
Qed.

Lemma prefix_parent_state_edge_count_nat__global_schedule :
  forall fuel n current,
    1 <= current ->
    n = current + Z.of_nat fuel ->
    ParentEdgeCount (PrefixParentState n current) = current - 1.
Proof.
  induction fuel as [|fuel IH]; intros n current Hcurrent Hn.
  - replace n with current by lia.
    apply target_chain_parent_edge_count__deficit_measure; [lia|].
    apply prefix_parent_state_target__attainment. lia.
  - assert (n = current + 1 + Z.of_nat fuel) as Hnext.
    { rewrite Nat2Z.inj_succ in Hn. lia. }
    pose proof (IH n (current + 1) ltac:(lia) Hnext) as Hcount_next.
    assert (ParentEdgeCount (PrefixParentState n (current + 1)) =
      ParentEdgeCount (PrefixParentState n current) + 1) as Hstep.
    { rewrite <- prefix_parent_state_step_replace__attainment by
        (rewrite Nat2Z.inj_succ in Hn; lia).
      apply parent_edge_count_replace_zero_to_nonzero__deficit_measure.
      - rewrite prefix_parent_state_length__attainment by lia.
        rewrite Nat2Z.inj_succ in Hn. lia.
      - rewrite prefix_parent_state_Znth__attainment by
          (rewrite Nat2Z.inj_succ in Hn; lia).
        destruct (Z_lt_dec current current); lia.
      - lia. }
    lia.
Qed.

Lemma prefix_parent_state_edge_count__global_schedule : forall n kept,
  1 <= kept <= n ->
  ParentEdgeCount (PrefixParentState n kept) = kept - 1.
Proof.
  intros n kept Hkept.
  apply (prefix_parent_state_edge_count_nat__global_schedule
    (Z.to_nat (n - kept)) n kept); [lia|].
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma removal_schedule_ready_edge_count__global_schedule :
  forall n chains removed order,
    RemovalScheduleReady n chains removed order ->
    ParentEdgeCount
      (ClearedParentState n chains (RemovedAfter removed order)) =
    ParentEdgeCount (ClearedParentState n chains removed) -
      Z.of_nat (length order).
Proof.
  intros n chains removed order Hready.
  induction Hready as [removed|
    removed child parent rest Hchild Hparent Hneq Hfresh Hlookup
    Hroot Hready IH].
  - unfold RemovedAfter. simpl. lia.
  - assert (ParentEdgeCount
      (ClearedParentState n chains (child :: removed)) =
      ParentEdgeCount (ClearedParentState n chains removed) - 1) as Hdrop.
    { rewrite <- cleared_parent_state_step_replace__dismantling_schedule
        by exact Hchild.
      apply parent_edge_count_replace_nonzero_to_zero__deficit_measure.
      - rewrite cleared_parent_state_length__dismantling_schedule by lia. lia.
      - rewrite cleared_parent_state_Znth__dismantling_schedule by lia.
        destruct (in_dec Z.eq_dec child removed); [contradiction|].
        rewrite Hlookup. lia. }
    rewrite removed_after_cons__global_schedule. simpl. lia.
Qed.

Lemma dismantling_order_length__global_schedule : forall n chains,
  1 <= n -> Pre n chains ->
  Z.of_nat (length (DismantlingOrder (usable_prefix chains) chains)) =
    n - Zlength chains - (usable_prefix chains - 1).
Proof.
  intros n chains Hn Hpre.
  pose proof (dismantling_order_ready__global_schedule
    n chains (usable_prefix chains) Hn Hpre) as Hready.
  pose proof (removal_schedule_ready_edge_count__global_schedule
    n chains [] (DismantlingOrder (usable_prefix chains) chains) Hready)
    as Hcount.
  rewrite cleared_parent_state_none__dismantling_schedule in Hcount.
  rewrite canonical_dismantling_endpoint__global_schedule in Hcount by assumption.
  rewrite prefix_parent_state_edge_count__global_schedule in Hcount by
    (apply usable_prefix_bounds__matryoshka_minimum; assumption).
  pose proof (canonical_parent_state_chain_parent__canonical_input
    n chains Hn Hpre) as Hparent.
  rewrite (chain_parent_edge_count__input_edges
    n chains (CanonicalParentState n chains) Hn Hpre Hparent) in Hcount.
  lia.
Qed.

Lemma canonical_dismantling_phase__global_schedule : forall n chains,
  1 <= n -> Pre n chains ->
  MatryoshkaDismantlingPhase n chains (usable_prefix chains)
    (CanonicalParentState n chains)
    (PrefixParentState n (usable_prefix chains))
    (CanonicalDismantlingStates n (usable_prefix chains) chains).
Proof.
  intros n chains Hn Hpre. unfold MatryoshkaDismantlingPhase.
  split.
  - apply canonical_parent_state_chain_parent__canonical_input; assumption.
  - split.
    + rewrite <- canonical_dismantling_endpoint__global_schedule by assumption.
      apply canonical_dismantling_trace__global_schedule; assumption.
    + rewrite canonical_dismantling_states_length__dismantling_schedule.
      rewrite (dismantling_order_length__global_schedule n chains Hn Hpre).
      pose proof (pre_total_length__matryoshka_minimum n chains Hn Hpre).
      lia.
Qed.

Lemma matryoshka_solver_result__global_schedule : forall n chains,
  1 <= n -> Pre n chains ->
  Spec n chains
    ((n - Zlength chains - (usable_prefix chains - 1)) +
     (n - usable_prefix chains)).
Proof.
  intros n chains Hn Hpre.
  eapply candidate_spec_from_dismantling__attainment
    with (init := CanonicalParentState n chains)
      (dismantle_states :=
        CanonicalDismantlingStates n (usable_prefix chains) chains);
    try eassumption.
  apply canonical_dismantling_phase__global_schedule; assumption.
Qed.

Lemma Zlength_Zrange_aux__loop_invariant : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low.
  induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__loop_invariant : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__loop_invariant. lia.
Qed.
Lemma Permutation_Zlength__loop_invariant : forall {A : Type} (l1 l2 : list A),
  Permutation l1 l2 -> Zlength l1 = Zlength l2.
Proof.
  intros A l1 l2 Hperm. rewrite !Zlength_correct.
  rewrite (Permutation_length Hperm). reflexivity.
Qed.
Lemma Znth_In__loop_invariant : forall {A : Type} (l : list A) d i,
  0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l d i Hi. unfold Znth.
  apply nth_In. rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Zlength_map__loop_invariant : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__loop_invariant : forall {A B : Type}
    (f : A -> B) l (da : A) (db : B) i,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l. induction l as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma row_Zlength_le_concat__loop_invariant : forall (rows : list (list Z)) row,
  In row rows -> Zlength row <= Zlength (concat rows).
Proof.
  intros rows row Hin.
  apply in_split in Hin as [before [after ->]].
  rewrite concat_app. simpl.
  rewrite !Zlength_app. pose proof (Zlength_nonneg (concat before)).
  pose proof (Zlength_nonneg (concat after)). lia.
Qed.
Lemma nonempty_rows_count_le_concat__loop_invariant : forall (rows : list (list Z)),
  Forall (fun row : list Z => row <> []) rows ->
  Zlength rows <= Zlength (concat rows).
Proof.
  intros rows Hrows. induction Hrows as [|row rows Hrow Hrows IH]; simpl.
  - reflexivity.
  - rewrite Zlength_cons, Zlength_app.
    destruct row as [|x xs]; [contradiction |].
    rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
Qed.
Lemma chain_collection_bounds__loop_invariant : forall n chains,
  1 <= n -> Pre n chains ->
  1 <= Zlength chains <= n /\
  forall j, 0 <= j < Zlength chains ->
    1 <= Znth j (ChainLengths chains) 0 <= n.
Proof.
  intros n chains Hn Hpre.
  destruct Hpre as [Hconcat [Hperm [Hnonempty Hmono]]].
  assert (Htotal : Zlength (concat chains) = n).
  { rewrite (Permutation_Zlength__loop_invariant _ _ Hperm).
    rewrite Zlength_Zrange__loop_invariant by lia. lia. }
  assert (Hchains : chains <> []).
  { intros ->. simpl in Hconcat. contradiction. }
  split.
  - split.
    + destruct chains as [|row rest]; [contradiction |].
      rewrite Zlength_cons. pose proof (Zlength_nonneg rest). lia.
    + rewrite <- Htotal.
      apply nonempty_rows_count_le_concat__loop_invariant. exact Hnonempty.
  - intros j Hj.
    unfold ChainLengths.
    rewrite (Znth_map__loop_invariant (fun row : list Z => Zlength row)
      chains [] 0 j Hj).
    assert (Hin : In (Znth j chains []) chains).
    { apply Znth_In__loop_invariant. exact Hj. }
    assert (Hrow : Znth j chains [] <> []).
    { rewrite Forall_forall in Hnonempty. apply Hnonempty. exact Hin. }
    split.
    + destruct (Znth j chains []) as [|x xs]; [contradiction |].
      rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
    + rewrite <- Htotal.
      apply row_Zlength_le_concat__loop_invariant. exact Hin.
Qed.
Lemma prefix_extraction_cost_step__loop_invariant : forall chains i,
  0 <= i < Zlength chains ->
  PrefixExtractionCost chains (i + 1) =
    PrefixExtractionCost chains i + Znth i (ChainLengths chains) 0 - 1.
Proof.
  intros chains i Hi.
  unfold PrefixExtractionCost at 1 2.
  rewrite (sublist_split 0 (i + 1) i (ChainLengths chains)) by
    (try unfold ChainLengths; try rewrite Zlength_map__loop_invariant; lia).
  rewrite (sublist_single 0) by
    (unfold ChainLengths; rewrite Zlength_map__loop_invariant; lia).
  rewrite map_app. simpl.
  induction (map (fun len : Z => len - 1)
    (sublist 0 i (ChainLengths chains))) as [|x xs IH]; simpl; lia.
Qed.
Lemma row_cost_formula__loop_invariant : forall (rows : list (list Z)),
  fold_right Z.add 0 (map (fun row => Zlength row - 1) rows) =
  Zlength (concat rows) - Zlength rows.
Proof.
  induction rows as [|row rows IH]; simpl.
  - reflexivity.
  - rewrite Zlength_app, Zlength_cons, IH. lia.
Qed.
Lemma map_sublist0__loop_invariant : forall {A B : Type}
    (f : A -> B) l hi,
  map f (sublist 0 hi l) = sublist 0 hi (map f l).
Proof.
  intros. unfold sublist. simpl. symmetry. apply firstn_map.
Qed.
Lemma prefix_extraction_cost_bound__loop_invariant : forall n chains upto,
  1 <= n -> Pre n chains -> 0 <= upto <= Zlength chains ->
  0 <= PrefixExtractionCost chains upto <= n.
Proof.
  intros n chains upto Hn Hpre Hupto.
  destruct Hpre as [Hconcat [Hperm [Hnonempty Hmono]]].
  assert (Htotal : Zlength (concat chains) = n).
  { rewrite (Permutation_Zlength__loop_invariant _ _ Hperm).
    rewrite Zlength_Zrange__loop_invariant by lia. lia. }
  assert (Hdecomp : chains =
      sublist 0 upto chains ++ sublist upto (Zlength chains) chains).
  { rewrite <- (sublist_self chains (Zlength chains)) at 1 by reflexivity.
    apply sublist_split; lia. }
  assert (Hprefix_nonempty :
      Forall (fun row : list Z => row <> []) (sublist 0 upto chains)).
  { rewrite Forall_forall in Hnonempty |- *.
    intros row Hin. apply Hnonempty.
    rewrite Hdecomp. apply in_or_app. left. exact Hin. }
  assert (Hprefix_len : Zlength (sublist 0 upto chains) = upto).
  { apply Zlength_sublist0. lia. }
  assert (Hprefix_concat :
      Zlength (concat (sublist 0 upto chains)) <= Zlength (concat chains)).
  { rewrite Hdecomp at 2. rewrite concat_app, Zlength_app.
    pose proof (Zlength_nonneg
      (concat (sublist upto (Zlength chains) chains))). lia. }
  unfold PrefixExtractionCost, ChainLengths.
  rewrite <- map_sublist0__loop_invariant.
  rewrite map_map.
  rewrite row_cost_formula__loop_invariant, Hprefix_len.
  pose proof (nonempty_rows_count_le_concat__loop_invariant _ Hprefix_nonempty).
  lia.
Qed.
