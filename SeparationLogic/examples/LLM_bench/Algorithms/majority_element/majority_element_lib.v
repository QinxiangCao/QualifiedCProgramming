Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint count (m : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eq_dec x m then 1 else 0) + count m xs
  end.

Definition IsMajorityElement (m : Z) (l : list Z) : Prop :=
  2 * (count m l) > Z.of_nat (length l).

Definition repeated (candidate vote : Z) : list Z :=
  repeat candidate (Z.to_nat vote).

Definition MajorityOnReduced (major candidate vote : Z) (rest : list Z) : Prop :=
  0 <= vote /\ IsMajorityElement major (repeated candidate vote ++ rest).

Lemma count_app : forall m l1 l2,
  count m (l1 ++ l2) = count m l1 + count m l2.
Proof.
  intros m l1.
  induction l1 as [| a l1 IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma count_repeat_nat : forall m candidate n,
  count m (repeat candidate n) =
  if Z.eq_dec m candidate then Z.of_nat n else 0.
Proof.
  intros m candidate n.
  induction n as [| n IH]; simpl.
  - destruct (Z.eq_dec m candidate); lia.
  - destruct (Z.eq_dec candidate m) as [Heq | Hneq].
    + subst m.
      destruct (Z.eq_dec candidate candidate) as [_ | Hfalse]; [| congruence].
      rewrite IH.
      destruct (Z.eq_dec candidate candidate) as [_ | Hfalse]; [lia | congruence].
    + destruct (Z.eq_dec candidate m) as [Hfalse | _].
      * congruence.
      * rewrite IH.
        destruct (Z.eq_dec m candidate) as [Hfalse | _].
        -- congruence.
        -- lia.
Qed.

Lemma repeated_nil : forall candidate,
  repeated candidate 0 = [].
Proof.
  intros. unfold repeated. reflexivity.
Qed.

Lemma repeat_snoc : forall (A : Type) (x : A) n,
  repeat x (S n) = repeat x n ++ [x].
Proof.
  intros A x n.
  rewrite <- Nat.add_1_r.
  rewrite repeat_app.
  simpl.
  reflexivity.
Qed.

Lemma repeated_succ : forall candidate vote,
  0 <= vote ->
  repeated candidate (vote + 1) = repeated candidate vote ++ [candidate].
Proof.
  intros candidate vote Hvote.
  unfold repeated.
  rewrite Z2Nat.inj_add by lia.
  change (Pos.to_nat 1) with 1.
  rewrite Nat.add_1_r.
  apply repeat_snoc.
Qed.

Lemma repeated_pred : forall candidate vote,
  0 < vote ->
  repeated candidate vote = repeated candidate (vote - 1) ++ [candidate].
Proof.
  intros candidate vote Hvote.
  replace vote with ((vote - 1) + 1) at 1 by lia.
  rewrite (repeated_succ candidate (vote - 1)) by lia.
  reflexivity.
Qed.

Lemma majority_on_reduced_init : forall major candidate rest,
  IsMajorityElement major rest ->
  MajorityOnReduced major candidate 0 rest.
Proof.
  intros major candidate rest Hmajor.
  unfold MajorityOnReduced.
  split; [lia |].
  rewrite repeated_nil.
  simpl.
  exact Hmajor.
Qed.

Lemma majority_on_reduced_reset : forall major candidate a rest,
  IsMajorityElement major (repeated candidate 0 ++ a :: rest) ->
  MajorityOnReduced major a 1 rest.
Proof.
  intros major candidate a rest Hmajor.
  unfold MajorityOnReduced.
  rewrite repeated_nil in Hmajor.
  simpl in Hmajor.
  split; [lia |].
  unfold repeated.
  simpl.
  exact Hmajor.
Qed.

Lemma majority_on_reduced_same : forall major candidate vote rest,
  0 <= vote ->
  IsMajorityElement major (repeated candidate vote ++ candidate :: rest) ->
  MajorityOnReduced major candidate (vote + 1) rest.
Proof.
  intros major candidate vote rest Hvote Hmajor.
  unfold MajorityOnReduced.
  split; [lia |].
  rewrite repeated_succ by lia.
  change (candidate :: rest) with ([candidate] ++ rest) in Hmajor.
  rewrite app_assoc in Hmajor.
  exact Hmajor.
Qed.

Lemma majority_on_reduced_cancel : forall major candidate a vote rest,
  0 < vote ->
  a <> candidate ->
  IsMajorityElement major (repeated candidate vote ++ a :: rest) ->
  MajorityOnReduced major candidate (vote - 1) rest.
Proof.
  intros major candidate a vote rest Hvote Hneq Hmajor.
  unfold MajorityOnReduced.
  split; [lia |].
  unfold repeated in *.
  unfold IsMajorityElement in *.
  rewrite count_app in Hmajor.
  rewrite count_app.
  rewrite count_repeat_nat in Hmajor.
  rewrite count_repeat_nat.
  simpl in Hmajor.
  rewrite length_app in Hmajor.
  rewrite length_app.
  rewrite repeat_length in Hmajor.
  rewrite repeat_length.
  simpl in Hmajor.
  destruct (Z.eq_dec major candidate) as [-> | Hmajor_candidate].
  - destruct (Z.eq_dec a candidate) as [Hfalse | Hac].
    + congruence.
    + change
        (match Z.of_nat (Z.to_nat vote) + (0 + count candidate rest) with
         | 0 => 0
         | Z.pos y' => Z.pos y'~0
         | Z.neg y' => Z.neg y'~0
         end)
        with (2 * (Z.of_nat (Z.to_nat vote) + (0 + count candidate rest))) in Hmajor.
      replace (2 * (Z.of_nat (Z.to_nat vote) + (0 + count candidate rest)))
        with (2 * (vote + count candidate rest)) in Hmajor by lia.
      replace (Z.of_nat (Z.to_nat vote + S (length rest)))
        with (vote + 1 + Z.of_nat (length rest)) in Hmajor by lia.
      replace (2 * (Z.of_nat (Z.to_nat (vote - 1)) + count candidate rest))
        with (2 * (vote - 1 + count candidate rest)) by lia.
      replace (Z.of_nat (Z.to_nat (vote - 1) + length rest))
        with (vote - 1 + Z.of_nat (length rest)) by lia.
      lia.
  - destruct (Z.eq_dec major candidate) as [Hfalse | _].
    + contradiction.
    + change
        (match 0 + ((if Z.eq_dec a major then 1 else 0) + count major rest) with
         | 0 => 0
         | Z.pos y' => Z.pos y'~0
         | Z.neg y' => Z.neg y'~0
         end)
        with (2 * (0 + ((if Z.eq_dec a major then 1 else 0) + count major rest))) in Hmajor.
      destruct (Z.eq_dec major a) as [-> | Hmajor_a].
      * replace (2 * (0 + ((if Z.eq_dec a a then 1 else 0) + count a rest)))
          with (2 * (1 + count a rest)) in Hmajor
          by (destruct (Z.eq_dec a a); [lia | contradiction]).
        replace (Z.of_nat (Z.to_nat vote + S (length rest)))
          with (vote + 1 + Z.of_nat (length rest)) in Hmajor by lia.
        replace (2 * (0 + count a rest))
          with (2 * count a rest) by lia.
        replace (Z.of_nat (Z.to_nat (vote - 1) + length rest))
          with (vote - 1 + Z.of_nat (length rest)) by lia.
        lia.
      * replace (2 * (0 + ((if Z.eq_dec a major then 1 else 0) + count major rest)))
          with (2 * count major rest) in Hmajor
          by (destruct (Z.eq_dec a major); [congruence | lia]).
        replace (Z.of_nat (Z.to_nat vote + S (length rest)))
          with (vote + 1 + Z.of_nat (length rest)) in Hmajor by lia.
        replace (2 * (0 + count major rest))
          with (2 * count major rest) by lia.
        replace (Z.of_nat (Z.to_nat (vote - 1) + length rest))
          with (vote - 1 + Z.of_nat (length rest)) by lia.
        nia.
Qed.

Lemma majority_of_repeated_eq : forall major candidate vote,
  0 <= vote ->
  IsMajorityElement major (repeated candidate vote) ->
  major = candidate.
Proof.
  intros major candidate vote Hvote Hmajor.
  unfold repeated in Hmajor.
  unfold IsMajorityElement in Hmajor.
  rewrite count_repeat_nat in Hmajor.
  rewrite repeat_length in Hmajor.
  destruct (Z.eq_dec major candidate) as [Heq | Hneq].
  - exact Heq.
  - lia.
Qed.

Lemma app_Znth_suffix_cons : forall (l1 l2 : list Z) i d,
  i = Zlength l1 ->
  i < Zlength (l1 ++ l2) ->
  exists h t,
    l2 = h :: t /\ Znth i (l1 ++ l2) d = h.
Proof.
  intros l1 l2 i d Hi Hlt.
  destruct l2 as [| h t].
  - rewrite Zlength_app, Zlength_nil in Hlt. lia.
  - exists h, t.
    split; [reflexivity |].
    subst i.
    rewrite app_Znth2 by lia.
    replace (Zlength l1 - Zlength l1) with 0 by lia.
    unfold Znth.
    simpl.
    reflexivity.
Qed.