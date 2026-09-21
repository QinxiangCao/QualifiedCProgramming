From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
Require Import MaxMinLib.MaxMin.
From Coq Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** The mathematical rotation is the length-[l] segment beginning at [start]
    in the doubled input.  It is independent of the candidate-elimination
    implementation used by the C function. *)
Definition MRRotation (l : list Z) (start : Z) : list Z :=
  sublist start (start + Zlength l) (l ++ l).

Definition MRValidStart (l : list Z) (start : Z) : Prop :=
  0 <= start < Zlength l.

Definition MRRotationValue
    (l : list Z) (start offset : Z) : Z :=
  Znth (start + offset) (l ++ l) 0.

Definition MRRotationPrefixEq
    (l : list Z) (left right prefix_len : Z) : Prop :=
  forall offset,
    0 <= offset < prefix_len ->
    MRRotationValue l left offset = MRRotationValue l right offset.

Definition MRRotationEq (l : list Z) (left right : Z) : Prop :=
  MRRotationPrefixEq l left right (Zlength l).

Definition MRRotationLt (l : list Z) (left right : Z) : Prop :=
  exists first_diff,
    0 <= first_diff < Zlength l /\
    MRRotationPrefixEq l left right first_diff /\
    MRRotationValue l left first_diff <
      MRRotationValue l right first_diff.

Definition MRRotationLe (l : list Z) (left right : Z) : Prop :=
  MRRotationLt l left right \/ MRRotationEq l left right.

(** [start] denotes a globally lexicographically minimal rotation. *)
Definition MRMinimalRotationAt (l : list Z) (start : Z) : Prop :=
  min_value_of_subset (MRRotationLe l) (MRValidStart l)
    (fun pos : Z => pos) start.

Lemma MRMinimalRotationAt_unfold l start :
  MRMinimalRotationAt l start <->
  MRValidStart l start /\
  forall other, MRValidStart l other -> MRRotationLe l start other.
Proof.
  unfold MRMinimalRotationAt, min_value_of_subset, min_object_of_subset.
  cbn beta. split.
  - intros [p [[Hp Hmin] Heq]]. subst p. auto.
  - intros [Hs Hmin]. exists start. auto.
Qed.

(** Both the lexicographic optimum and its tie-breaking index use MinMax. *)
Definition MRFirstMinimalRotationAt (l : list Z) (start : Z) : Prop :=
  MRMinimalRotationAt l start /\
  min_value_of_subset Z.le
    (fun other => MRValidStart l other /\ MRRotationEq l start other)
    (fun pos : Z => pos) start.

Lemma MRFirstMinimalRotationAt_unfold l start :
  MRFirstMinimalRotationAt l start <->
  MRMinimalRotationAt l start /\
  forall other, MRValidStart l other -> MRRotationEq l start other -> start <= other.
Proof.
  unfold MRFirstMinimalRotationAt, min_value_of_subset, min_object_of_subset.
  cbn beta. split.
  - intros [Hmin [p [[Hp Hall] Heq]]]. subst p.
    split; [exact Hmin | intros q Hq Heq; apply Hall; split; assumption].
  - intros [Hmin Htie]. split; [exact Hmin |]. exists start.
    split; [split | reflexivity].
    + split.
      * apply MRMinimalRotationAt_unfold in Hmin. tauto.
      * unfold MRRotationEq, MRRotationPrefixEq. intros. reflexivity.
    + intros q [Hq Heq]. apply Htie; assumption.
Qed.

(** Stable mathematical state of the two-candidate elimination phase.

    The unique first minimal start is either one of the two live candidates,
    or it has not yet crossed the monotonically advancing candidate frontier.
    In the latter case the two current rotations cannot already be identical;
    otherwise the first of them would be the canonical answer. *)
Definition MRCandidateState
    (l : list Z) (best i j : Z) : Prop :=
  best = i \/
  best = j \/
  (Z.max i j <= best /\ ~ MRRotationEq l i j).

From Coq Require Import Lia.
Lemma Znth_double_add_length__candidate_transitions :
  forall (l : list Z) z,
    0 <= z < Zlength l ->
    Znth (z + Zlength l) (l ++ l) 0 = Znth z (l ++ l) 0.
Proof.
  intros l z Hz.
  rewrite app_Znth2 by lia.
  replace (z + Zlength l - Zlength l) with z by lia.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.
Lemma MRRotationValue_sub_length__candidate_transitions :
  forall (l : list Z) start offset,
    Zlength l <= start ->
    0 <= offset ->
    start + offset < 2 * Zlength l ->
    MRRotationValue l (start - Zlength l) offset =
      MRRotationValue l start offset.
Proof.
  intros l start offset Hstart Hoff Hupper.
  unfold MRRotationValue.
  replace (start + offset) with
      ((start - Zlength l + offset) + Zlength l) by lia.
  symmetry.
  apply Znth_double_add_length__candidate_transitions.
  lia.
Qed.
Lemma MRRotationEq_sym__candidate_transitions :
  forall l a b,
    MRRotationEq l a b -> MRRotationEq l b a.
Proof.
  unfold MRRotationEq, MRRotationPrefixEq.
  intros l a b Hab offset Hoff.
  symmetry.
  apply Hab.
  exact Hoff.
Qed.
Lemma MRRotationPrefixEq_sym__candidate_transitions :
  forall l a b k,
    MRRotationPrefixEq l a b k -> MRRotationPrefixEq l b a k.
Proof.
  unfold MRRotationPrefixEq.
  intros l a b k Hab offset Hoff.
  symmetry.
  apply Hab.
  exact Hoff.
Qed.
Lemma MRRotationEq_shift__candidate_transitions :
  forall l a b shift,
    0 < Zlength l ->
    0 <= a ->
    0 <= b ->
    0 <= shift ->
    a + shift < Zlength l ->
    b + shift < Zlength l ->
    MRRotationEq l a b ->
    MRRotationEq l (a + shift) (b + shift).
Proof.
  unfold MRRotationEq, MRRotationPrefixEq.
  intros l a b shift Hlen Ha Hb Hshift Hashift Hbshift Heq offset Hoff.
  destruct (Z_lt_ge_dec (shift + offset) (Zlength l)) as [Hnowrap | Hwrap].
  - specialize (Heq (shift + offset) ltac:(lia)).
    unfold MRRotationValue in *.
    replace (a + shift + offset) with (a + (shift + offset)) by lia.
    replace (b + shift + offset) with (b + (shift + offset)) by lia.
    exact Heq.
  - specialize (Heq (shift + offset - Zlength l) ltac:(lia)).
    unfold MRRotationValue in *.
    replace (a + shift + offset) with
        ((a + (shift + offset - Zlength l)) + Zlength l) by lia.
    replace (b + shift + offset) with
        ((b + (shift + offset - Zlength l)) + Zlength l) by lia.
    rewrite !Znth_double_add_length__candidate_transitions by lia.
    exact Heq.
Qed.
Lemma MRRotationLt_not_le_rev__candidate_transitions :
  forall l a b,
    MRRotationLt l a b -> ~ MRRotationLe l b a.
Proof.
  intros l a b [da [Hda [Hab Hlt]]] Hle.
  destruct Hle as [[db [Hdb [Hba Hgt]]] | Heq].
  - unfold MRRotationPrefixEq in Hab, Hba.
    destruct (Z.lt_trichotomy da db) as [Horder | [Horder | Horder]].
    + specialize (Hba da ltac:(lia)).
      lia.
    + subst db.
      lia.
    + specialize (Hab db ltac:(lia)).
      lia.
  - unfold MRRotationEq, MRRotationPrefixEq in Heq.
    specialize (Heq da Hda).
    lia.
Qed.
Lemma MRRotationEq_frontier_neq__candidate_transitions :
  forall l best x y,
    MRFirstMinimalRotationAt l best ->
    MRValidStart l x ->
    MRValidStart l y ->
    Z.max x y <= best ->
    x <> y ->
    ~ MRRotationEq l x y.
Proof.
  intros l best x y Hfirst Hx Hy Hfront Hxy Heq.
  rewrite MRFirstMinimalRotationAt_unfold, MRMinimalRotationAt_unfold in Hfirst.
  destruct Hfirst as [[[Hbest0 Hbestn] Hminimal] Htie].
  destruct Hx as [Hx0 Hxn].
  destruct Hy as [Hy0 Hyn].
  destruct (Z_lt_ge_dec x y) as [Hlt | Hge].
  - rewrite Z.max_r in Hfront by lia.
    pose proof
      (MRRotationEq_shift__candidate_transitions
         l x y (best - y) ltac:(lia) ltac:(lia) ltac:(lia)
         ltac:(lia) ltac:(lia) ltac:(lia) Heq) as Hshift.
    replace (x + (best - y)) with (best - (y - x)) in Hshift by lia.
    replace (y + (best - y)) with best in Hshift by lia.
    pose proof
      (Htie (best - (y - x)) ltac:(unfold MRValidStart; lia)
         (MRRotationEq_sym__candidate_transitions _ _ _ Hshift)) as Horder.
    lia.
  - assert (y < x) by lia.
    rewrite Z.max_l in Hfront by lia.
    pose proof (MRRotationEq_sym__candidate_transitions _ _ _ Heq) as Heyx.
    pose proof
      (MRRotationEq_shift__candidate_transitions
         l y x (best - x) ltac:(lia) ltac:(lia) ltac:(lia)
         ltac:(lia) ltac:(lia) ltac:(lia) Heyx) as Hshift.
    replace (y + (best - x)) with (best - (x - y)) in Hshift by lia.
    replace (x + (best - x)) with best in Hshift by lia.
    pose proof
      (Htie (best - (x - y)) ltac:(unfold MRValidStart; lia)
         (MRRotationEq_sym__candidate_transitions _ _ _ Hshift)) as Horder.
    lia.
Qed.
Lemma MRCandidateState_swap__candidate_transitions :
  forall l best i j,
    MRCandidateState l best i j -> MRCandidateState l best j i.
Proof.
  intros l best i j Hstate.
  unfold MRCandidateState in *.
  destruct Hstate as [Hbi | [Hbj | [Hfront Hneq]]].
  - right; left; exact Hbi.
  - left; exact Hbj.
  - right; right; split.
    + rewrite Z.max_comm. exact Hfront.
    + intro Heq.
      apply Hneq.
      apply MRRotationEq_sym__candidate_transitions.
      exact Heq.
Qed.
Lemma MRFirstMinimal_excludes_left_interval__candidate_transitions :
  forall l best i j k,
    MRFirstMinimalRotationAt l best ->
    MRValidStart l i ->
    MRValidStart l j ->
    0 <= k < Zlength l ->
    MRRotationPrefixEq l i j k ->
    MRRotationValue l j k < MRRotationValue l i k ->
    i <= best ->
    i + k < best.
Proof.
  intros l best i j k Hfirst Hi Hj Hk Hprefix Hmismatch Hibest.
  rewrite MRFirstMinimalRotationAt_unfold, MRMinimalRotationAt_unfold in Hfirst.
  destruct Hfirst as [Hminimal Htie].
  destruct Hminimal as [Hbestvalid Hbestle].
  destruct Hbestvalid as [Hbest0 Hbestn].
  destruct Hi as [Hi0 Hin].
  destruct Hj as [Hj0 Hjn].
  destruct Hk as [Hk0 Hkn].
  destruct (Z_lt_ge_dec (i + k) best) as [Hdone | Hinside].
  - exact Hdone.
  - set (d := best - i).
    assert (Hd : 0 <= d <= k) by (unfold d; lia).
    destruct (Z_lt_ge_dec (j + d) (Zlength l)) as [Hrawlt | Hrawge].
    + assert (Huvalid : MRValidStart l (j + d)).
      { unfold MRValidStart. lia. }
      assert (Hloses : MRRotationLt l (j + d) best).
      {
        unfold MRRotationLt.
        exists (k - d).
        split; [lia |].
        split.
        - unfold MRRotationPrefixEq.
          intros offset Hoff.
          specialize (Hprefix (d + offset) ltac:(lia)).
          replace (MRRotationValue l (j + d) offset)
            with (MRRotationValue l j (d + offset)) by
              (unfold MRRotationValue; f_equal; lia).
          replace (MRRotationValue l best offset)
            with (MRRotationValue l i (d + offset)) by
              (unfold MRRotationValue; f_equal; unfold d; lia).
          symmetry.
          exact Hprefix.
        - replace (MRRotationValue l (j + d) (k - d))
            with (MRRotationValue l j k) by
              (unfold MRRotationValue; f_equal; lia).
          replace (MRRotationValue l best (k - d))
            with (MRRotationValue l i k) by
              (unfold MRRotationValue; f_equal; unfold d; lia).
          exact Hmismatch.
      }
      exfalso.
      apply (MRRotationLt_not_le_rev__candidate_transitions _ _ _ Hloses).
      apply Hbestle.
      exact Huvalid.
    + assert (Huvalid : MRValidStart l (j + d - Zlength l)).
      { unfold MRValidStart. lia. }
      assert (Hloses : MRRotationLt l (j + d - Zlength l) best).
      {
        unfold MRRotationLt.
        exists (k - d).
        split; [lia |].
        split.
        - unfold MRRotationPrefixEq.
          intros offset Hoff.
          specialize (Hprefix (d + offset) ltac:(lia)).
          rewrite (MRRotationValue_sub_length__candidate_transitions
                     l (j + d) offset) by lia.
          replace (MRRotationValue l (j + d) offset)
            with (MRRotationValue l j (d + offset)) by
              (unfold MRRotationValue; f_equal; lia).
          replace (MRRotationValue l best offset)
            with (MRRotationValue l i (d + offset)) by
              (unfold MRRotationValue; f_equal; unfold d; lia).
          symmetry.
          exact Hprefix.
        - rewrite (MRRotationValue_sub_length__candidate_transitions
                     l (j + d) (k - d)) by lia.
          replace (MRRotationValue l (j + d) (k - d))
            with (MRRotationValue l j k) by
              (unfold MRRotationValue; f_equal; lia).
          replace (MRRotationValue l best (k - d))
            with (MRRotationValue l i k) by
              (unfold MRRotationValue; f_equal; unfold d; lia).
          exact Hmismatch.
      }
      exfalso.
      apply (MRRotationLt_not_le_rev__candidate_transitions _ _ _ Hloses).
      apply Hbestle.
      exact Huvalid.
Qed.
Lemma MRCandidateState_advance_left__candidate_transitions :
  forall l best i j k,
    MRFirstMinimalRotationAt l best ->
    MRValidStart l i ->
    MRValidStart l j ->
    0 <= k < Zlength l ->
    MRRotationPrefixEq l i j k ->
    MRRotationValue l j k < MRRotationValue l i k ->
    MRCandidateState l best i j ->
    ((i + k + 1 = j ->
        MRCandidateState l best (i + k + 2) j) /\
     (i + k + 1 <> j ->
        MRCandidateState l best (i + k + 1) j)).
Proof.
  intros l best i j k Hfirst Hi Hj Hk Hprefix Hmismatch Hstate.
  pose proof Hfirst as Hfirst_saved.
  pose proof Hi as Hi_saved.
  pose proof Hj as Hj_saved.
  pose proof Hk as Hk_saved.
  rewrite MRFirstMinimalRotationAt_unfold, MRMinimalRotationAt_unfold in Hfirst.
  destruct Hfirst as [[[Hbest0 Hbestn] Hminimal] Htie].
  destruct Hi as [Hi0 Hin].
  destruct Hj as [Hj0 Hjn].
  destruct Hk as [Hk0 Hkn].
  unfold MRCandidateState in Hstate.
  destruct Hstate as [Hbi | [Hbj | [Hfront Hneq]]].
  - subst best.
    pose proof
      (MRFirstMinimal_excludes_left_interval__candidate_transitions
         l i i j k Hfirst_saved Hi_saved Hj_saved Hk_saved Hprefix
         Hmismatch ltac:(lia)) as Hcontra.
    lia.
  - subst best.
    split; intro Hbranch; unfold MRCandidateState.
    + right; left; reflexivity.
    + right; left; reflexivity.
  - assert (Hibest : i <= best).
    { eapply Z.le_trans; [apply Z.le_max_l | exact Hfront]. }
    assert (Hjbest : j <= best).
    { eapply Z.le_trans; [apply Z.le_max_r | exact Hfront]. }
    pose proof
      (MRFirstMinimal_excludes_left_interval__candidate_transitions
         l best i j k Hfirst_saved Hi_saved Hj_saved Hk_saved Hprefix
         Hmismatch Hibest) as Hadvance.
    split.
    + intro Hcollision.
      destruct (Z.eq_dec best j) as [Hbestj | Hbestj].
      * unfold MRCandidateState.
        right; left; exact Hbestj.
      * unfold MRCandidateState.
        right; right.
        split.
        -- rewrite Z.max_l by lia.
           lia.
        -- apply (MRRotationEq_frontier_neq__candidate_transitions
                    l best (i + k + 2) j Hfirst_saved).
           ++ unfold MRValidStart. lia.
           ++ exact Hj_saved.
           ++ rewrite Z.max_l by lia. lia.
           ++ lia.
    + intro Hnoncollision.
      unfold MRCandidateState.
      right; right.
      split.
      * apply Z.max_lub; lia.
      * apply (MRRotationEq_frontier_neq__candidate_transitions
                  l best (i + k + 1) j Hfirst_saved).
        -- unfold MRValidStart. lia.
        -- exact Hj_saved.
        -- apply Z.max_lub; lia.
        -- exact Hnoncollision.
Qed.
Lemma MRCandidateState_advance_right__candidate_transitions :
  forall l best i j k,
    MRFirstMinimalRotationAt l best ->
    MRValidStart l i ->
    MRValidStart l j ->
    0 <= k < Zlength l ->
    MRRotationPrefixEq l i j k ->
    MRRotationValue l i k < MRRotationValue l j k ->
    MRCandidateState l best i j ->
    ((j + k + 1 = i ->
        MRCandidateState l best i (j + k + 2)) /\
     (j + k + 1 <> i ->
        MRCandidateState l best i (j + k + 1))).
Proof.
  intros l best i j k Hfirst Hi Hj Hk Hprefix Hmismatch Hstate.
  pose proof
    (MRCandidateState_advance_left__candidate_transitions
       l best j i k Hfirst Hj Hi Hk
       (MRRotationPrefixEq_sym__candidate_transitions _ _ _ _ Hprefix)
       Hmismatch
       (MRCandidateState_swap__candidate_transitions _ _ _ _ Hstate))
    as [Hcollision Hnoncollision].
  split; intro Hbranch.
  - apply MRCandidateState_swap__candidate_transitions.
    apply Hcollision.
    exact Hbranch.
  - apply MRCandidateState_swap__candidate_transitions.
    apply Hnoncollision.
    exact Hbranch.
Qed.
Lemma MRRotationEq_sym__candidate_boundaries :
  forall l i j,
    MRRotationEq l i j ->
    MRRotationEq l j i.
Proof.
  intros l i j Heq.
  unfold MRRotationEq, MRRotationPrefixEq in *.
  intros offset Hoff.
  symmetry.
  apply Heq; exact Hoff.
Qed.
Lemma MRRotationEq_zero_one_all__candidate_boundaries :
  forall l,
    1 <= Zlength l ->
    MRRotationEq l 0 1 ->
    forall start,
      MRValidStart l start ->
      MRRotationEq l start 0.
Proof.
  intros l Hlen Heq start Hstart.
  unfold MRRotationEq, MRRotationPrefixEq, MRRotationValue in Heq.
  assert (Hchain :
    forall z,
      0 <= z <= Zlength l ->
      Znth z (l ++ l) 0 = Znth 0 (l ++ l) 0).
  {
    intros z Hz.
    set (m := Z.to_nat z).
    assert (Hzm : z = Z.of_nat m).
    { unfold m. lia. }
    rewrite Hzm in Hz |- *.
    clearbody m.
    clear Hzm z.
    revert Hz.
    induction m as [|m IH]; intros Hz.
    - reflexivity.
    - rewrite Nat2Z.inj_succ in *.
      specialize (Heq (Z.of_nat m) ltac:(lia)).
      replace (0 + Z.of_nat m) with (Z.of_nat m) in Heq by lia.
      replace (1 + Z.of_nat m) with (Z.succ (Z.of_nat m)) in Heq by lia.
      rewrite <- Heq.
      apply IH; lia.
  }
  assert (Hall :
    forall z,
      0 <= z < 2 * Zlength l ->
      Znth z (l ++ l) 0 = Znth 0 (l ++ l) 0).
  {
    intros z Hz.
    destruct (Z_lt_ge_dec z (Zlength l)) as [Hzlt | Hzge].
    - apply Hchain; lia.
    - rewrite app_Znth2 by lia.
      rewrite <- (app_Znth1 0 l l (z - Zlength l)) by lia.
      apply Hchain; lia.
  }
  unfold MRRotationEq, MRRotationPrefixEq, MRRotationValue.
  intros offset Hoff.
  transitivity (Znth 0 (l ++ l) 0).
  - apply Hall.
    unfold MRValidStart in Hstart.
    lia.
  - symmetry.
    apply Hall; lia.
Qed.
Lemma MRCandidateState_initial__candidate_boundaries :
  forall l best,
    1 <= Zlength l ->
    MRFirstMinimalRotationAt l best ->
    MRCandidateState l best 0 1.
Proof.
  intros l best Hlen Hfirst.
  rewrite MRFirstMinimalRotationAt_unfold, MRMinimalRotationAt_unfold in Hfirst.
  destruct Hfirst as [[Hvalid Hminimal] Htie].
  destruct (Z.eq_dec best 0) as [Hbest | Hbest].
  - left; exact Hbest.
  - destruct (Z.eq_dec best 1) as [Hbest1 | Hbest1].
    + right; left; exact Hbest1.
    + right; right.
      split.
      * change (1 <= best).
        unfold MRValidStart in Hvalid.
        lia.
      * intro Heq01.
        pose proof
          (MRRotationEq_zero_one_all__candidate_boundaries
             l Hlen Heq01 best Hvalid) as Heqbest0.
        specialize (Htie 0 ltac:(unfold MRValidStart; lia) Heqbest0).
        unfold MRValidStart in Hvalid.
        lia.
Qed.
Lemma MRCandidateState_equal_exit__candidate_boundaries :
  forall l best i j,
    MRValidStart l i ->
    MRValidStart l j ->
    i <> j ->
    MRFirstMinimalRotationAt l best ->
    MRCandidateState l best i j ->
    MRRotationEq l i j ->
    (i < j -> i = best) /\ (i >= j -> j = best).
Proof.
  intros l best i j Hvalidi Hvalidj Hneq Hfirst Hstate Heq.
  rewrite MRFirstMinimalRotationAt_unfold, MRMinimalRotationAt_unfold in Hfirst.
  destruct Hfirst as [_ Htie].
  unfold MRCandidateState in Hstate.
  destruct Hstate as [Hbest | [Hbest | [_ Hne]]].
  - split.
    + intro; lia.
    + intro Hge.
      assert (Hbest_le_j : best <= j).
      { apply (Htie j Hvalidj). rewrite Hbest. exact Heq. }
      lia.
  - split.
    + intro Hlt.
      assert (Hbest_le_i : best <= i).
      {
        apply (Htie i Hvalidi).
        rewrite Hbest.
        apply MRRotationEq_sym__candidate_boundaries.
        exact Heq.
      }
      lia.
    + intro; lia.
  - contradiction.
Qed.
Lemma MRRotation_Zlength__output_finalization :
  forall l start,
    MRValidStart l start ->
    Zlength (MRRotation l start) = Zlength l.
Proof.
  intros l start Hstart.
  unfold MRValidStart in Hstart.
  unfold MRRotation.
  rewrite Zlength_sublist by (rewrite Zlength_app; lia).
  lia.
Qed.
Lemma MRRotation_Znth__output_finalization :
  forall l start offset,
    MRValidStart l start ->
    0 <= offset < Zlength l ->
    Znth offset (MRRotation l start) 0 =
      Znth (start + offset) (l ++ l) 0.
Proof.
  intros l start offset Hstart Hoff.
  unfold MRValidStart in Hstart.
  unfold MRRotation.
  rewrite Znth_sublist by lia.
  f_equal.
  lia.
Qed.
