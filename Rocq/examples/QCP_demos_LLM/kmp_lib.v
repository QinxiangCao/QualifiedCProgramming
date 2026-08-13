Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Require Import String.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.
Require Import AUXLib.ListLib.

Section KMP.

Context {A: Type} (default: A).

Inductive inner_step
            (str: list A) (vnext: list Z) (ch: A): Z -> Z -> Prop :=
| inner_step_forward: forall j,
    j >= 0 ->
    ch <> Znth j str default ->
    inner_step str vnext ch j (Znth j vnext 0).

Definition inner_steps
             (str: list A) (vnext: list Z) (ch: A): Z -> Z -> Prop :=
  clos_refl_trans (inner_step str vnext ch).

Inductive constr_step (str: list A): list Z -> list Z -> Prop :=
| constr_step_match: forall vnext i j,
    j >= 0 ->
    i + 1 = Zlength vnext ->
    inner_steps str vnext (Znth i str default) (Znth i vnext 0) j ->
    Znth i str default = Znth j str default ->
    constr_step str vnext (vnext ++ [j + 1])
| constr_step_no_match: forall vnext i,
    i + 1 = Zlength vnext ->
    inner_steps str vnext (Znth i str default) (Znth i vnext 0) (-1) ->
    constr_step str vnext (vnext ++ [0]).

Definition constr_steps
             (str: list A) (vnext: list Z): Prop :=
  clos_refl_trans (constr_step str) [-1] vnext.

Definition constr_rel (str: list A) (vnext: list Z): Prop :=
  constr_steps str vnext /\
  Zlength vnext = Zlength str + 1.

Inductive match_step
            (str_p str_t: list A) (vnext: list Z):
            Z * Z -> Z * Z -> Prop :=
| match_step_match: forall i j1 j2,
    j1 < Zlength str_p ->
    j2 >= 0 ->
    inner_steps str_p vnext (Znth i str_t default) j1 j2 ->
    Znth i str_t default = Znth j2 str_p default ->
    match_step str_p str_t vnext (i, j1) (i + 1, j2 + 1)
| match_step_no_match: forall i j,
    j < Zlength str_p ->
    inner_steps str_p vnext (Znth i str_t default) j (-1) ->
    match_step str_p str_t vnext (i, j) (i + 1, 0).

Definition match_steps
             (str_p str_t: list A) (vnext: list Z) (i j: Z): Prop :=
  clos_refl_trans (match_step str_p str_t vnext) (1, 0) (i, j).

Definition occur
             (str_p str_t: list A) (k: Z): Prop :=
  exists s1 s2,
    Zlength s1 = k /\
    str_t = s1 ++ str_p ++ s2.

Definition fst_occur
             (str_p str_t: list A) (k: Z): Prop :=
  (occur str_p str_t k /\
   forall k', occur str_p str_t k' -> k <= k') \/
  (k = -1 /\
   forall k', ~ occur str_p str_t k').

Definition all_char (str: list Z): Prop :=
  forall k,
    0 <= k < Zlength str ->
    - 128 <= Znth k str 0 <= 127.

Record in_range (vnext: list Z): Prop := {
  len_nonneg:
    Zlength vnext > 0;
  in_range_0:
    Znth 0 vnext 0 = -1;
  in_range_pos:
    forall k,
      0 < k < Zlength vnext ->
      0 <= Znth k vnext 0 < k
}.

Notation "H '.(len_nonneg)'" := (len_nonneg _ H)
  (at level 1).

Notation "H '.(in_range_0)'" := (in_range_0 _ H)
  (at level 1).

Notation "H '.(in_range_pos)'" := (in_range_pos _ H)
  (at level 1).

Lemma in_range_gen: forall vnext, in_range vnext ->
  forall k,
    0 <= k < Zlength vnext -> - 1 <= Znth k vnext 0 < k.
Proof.
  intros.
  destruct (classic (k = 0)).
  + subst k.
    rewrite H.(in_range_0).
    lia.
  + pose proof H.(in_range_pos) k ltac:(lia).
    lia.
Qed.

Notation "H '.(in_range_gen)'" := (in_range_gen _ H)
  (at level 1).

Lemma inner_step_j_decr:
  forall str vnext ch j j',
    inner_step str vnext ch j j' ->
    in_range vnext ->
    -1 <= j < Zlength vnext ->
    -1 <= j' < j.
Proof.
  intros.
  inversion H; subst.
  pose proof H0.(in_range_gen) j ltac:(lia).
  lia.
Qed.

Lemma inner_steps_j_decr:
  forall str vnext ch j j',
    inner_steps str vnext ch j j' ->
    in_range vnext ->
    -1 <= j < Zlength vnext ->
    -1 <= j' <= j.
Proof.
  intros.
  unfold inner_steps in H.
  induction_1n H.
  + lia.
  + pose proof inner_step_j_decr _ _ _ _ _ H2 H0 H1.
    specialize (IHrt H0).
    lia.
Qed.

Lemma inner_steps_in_range_for_constr:
  forall str vnext ch j,
    inner_steps str vnext ch (Znth (Zlength vnext - 1) vnext 0) j ->
    in_range vnext ->
    -1 <= j < Zlength vnext - 1.
Proof.
  intros.
  pose proof H0.(len_nonneg).
  pose proof H0.(in_range_gen) (Zlength vnext - 1) ltac:(lia).
  pose proof inner_steps_j_decr _ _ _ _ _ H H0 ltac:(lia).
  lia.
Qed.

Lemma constr_step_len_incr:
  forall str vnext vnext',
    constr_step str vnext vnext' ->
    Zlength vnext' = Zlength vnext + 1.
Proof.
  intros.
  inversion H; subst.
  + rewrite Zlength_app.
    reflexivity.
  + rewrite Zlength_app.
    reflexivity.
Qed.

Lemma constr_step_in_range_0:
  forall str vnext vnext',
    constr_step str vnext vnext' ->
    in_range vnext ->
    Znth 0 vnext' 0 = -1.
Proof.
  intros.
  pose proof H0.(len_nonneg).
  inversion H; subst.
  + rewrite app_Znth1 by lia.
    apply H0.(in_range_0).
  + rewrite app_Znth1 by lia.
    apply H0.(in_range_0).
Qed.

Lemma constr_step_in_range_pos:
  forall str vnext vnext',
    constr_step str vnext vnext' ->
    in_range vnext ->
    (forall k, 0 < k < Zlength vnext' -> 0 <= Znth k vnext' 0 < k).
Proof.
  intros.
  pose proof constr_step_len_incr _ _ _ H.
  inversion H; subst.
  + destruct (classic (k = i + 1)).
    - subst k.
      rewrite app_Znth2 by lia.
      replace (i + 1 - Zlength vnext) with 0 by lia.
      change (Znth 0 [j + 1] 0) with (j + 1).
      pose proof H0.(in_range_gen) i ltac:(lia).
      pose proof inner_steps_j_decr _ _ _ _ _ H5 H0 ltac:(lia).
      lia.
    - rewrite app_Znth1 by lia.
      pose proof H0.(in_range_pos) k ltac:(lia).
      tauto.
  + destruct (classic (k = i + 1)).
    - subst k.
      rewrite app_Znth2 by lia.
      replace (i + 1 - Zlength vnext) with 0 by lia.
      change (Znth 0 [0] 0) with 0.
      lia.
    - rewrite app_Znth1 by lia.
      pose proof H0.(in_range_pos) k ltac:(lia).
      tauto.
Qed.

Lemma constr_step_in_range:
  forall str vnext vnext',
    constr_step str vnext vnext' ->
    in_range vnext ->
    Zlength vnext' = Zlength vnext + 1 /\ in_range vnext'.
Proof.
  intros.
  split; [| split].
  + pose proof constr_step_len_incr _ _ _ H.
    tauto.
  + pose proof constr_step_len_incr _ _ _ H.
    pose proof H0.(len_nonneg).
    lia.
  + pose proof constr_step_in_range_0 _ _ _ H H0.
    tauto.
  + pose proof constr_step_in_range_pos _ _ _ H H0.
    tauto.
Qed.

Lemma clos_refl_trans_constr_step_in_range:
  forall str vnext vnext',
    clos_refl_trans (constr_step str) vnext vnext' ->
    in_range vnext ->
    Zlength vnext <= Zlength vnext' /\ in_range vnext'.
Proof.
  intros.
  induction_1n H.
  + split; [lia | tauto].
  + pose proof constr_step_in_range _ _ _ H1 H0.
    pose proof IHrt ltac:(tauto).
    split; [lia | tauto].
Qed.

Lemma constr_steps_in_range:
  forall str vnext,
    constr_steps str vnext ->
    in_range vnext.
Proof.
  intros.
  unfold constr_steps in H.
  pose proof clos_refl_trans_constr_step_in_range _ _ _ H.
  assert (in_range [-1]). {
    split.
    + reflexivity.
    + reflexivity.
    + change (Zlength [-1]) with 1.
      intros; lia.
  }
  pose proof H0 H1 as [i ?].
  tauto.
Qed.

Lemma constr_rel_in_range:
  forall str vnext,
    constr_rel str vnext ->
    Zlength vnext = Zlength str + 1 /\ in_range vnext.
Proof.
  intros.
  destruct H.
  pose proof constr_steps_in_range _ _ H.
  tauto.
Qed.

Lemma match_step_in_range:
  forall (str_p str_t: list A) vnext i j i' j',
    match_step str_p str_t vnext (i, j) (i', j') ->
    Zlength vnext = Zlength str_p + 1 /\ in_range vnext ->
    0 <= j <= i ->
    0 <= j' <= i'.
Proof.
  intros.
  inversion H; subst.
  + pose proof inner_steps_j_decr _ _ _ _ _ H8 ltac:(tauto).
    lia.
  + lia.
Qed.

Lemma clos_refl_trans_match_step_in_range:
  forall (str_p str_t: list A) vnext i j i' j',
    clos_refl_trans (match_step str_p str_t vnext) (i, j) (i', j') ->
    Zlength vnext = Zlength str_p + 1 /\ in_range vnext ->
    0 <= j <= i ->
    0 <= j' <= i'.
Proof.
  intros.
  induction_1n H.
  + tauto.
  + pose proof match_step_in_range _ _ _ _ _ _ _ H2 H0 ltac:(lia).
    specialize (IHrt H3 H0).
    tauto.
Qed.

Lemma match_steps_in_range:
  forall (str_p str_t: list A) vnext i j,
    match_steps str_p str_t vnext i j ->
    Zlength vnext = Zlength str_p + 1 /\ in_range vnext ->
    0 <= j <= i.
Proof.
  intros.
  unfold match_steps in H.
  pose proof clos_refl_trans_match_step_in_range _ _ _ _ _ _ _ H H0.
  lia.
Qed.

Definition presuffix
             (str1 str2: list A) (i1 i2: Z) :=
  forall k,
    0 <= k < i1 ->
    Znth k str1 default = Znth (k + (i2 - i1)) str2 default.

Definition presuffix_ub
             (str1 str2: list A) (i1 i2: Z) :=
  forall k, 0 <= k <= Zlength str1 -> presuffix str1 str2 k i2 -> k <= i1.

Definition greatest_presuffix
             (str1 str2: list A) (i1 i2: Z) :=
  presuffix str1 str2 i1 i2 /\
  presuffix_ub str1 str2 i1 i2.

Lemma prefix_presuffix1:
  forall (str1 str2: list A) (i1' i1 i2: Z),
    i1' <= i1 ->
    (presuffix str1 str2 i1' i2 <->
     presuffix (sublist 0 i1 str1) str2 i1' i2).
Proof.
  intros.
  split; intros ? k ?; specialize (H0 k H1).
  + rewrite Znth_sublist by lia.
    replace (k + 0) with k by lia.
    tauto.
  + rewrite Znth_sublist in H0 by lia.
    replace (k + 0) with k in H0 by lia.
    tauto.
Qed.

Lemma prefix_presuffix2:
  forall (str1 str2: list A) (i1 i2' i2: Z),
    i1 <= i2' <= i2 ->
    (presuffix str1 str2 i1 i2' <->
     presuffix str1 (sublist 0 i2 str2) i1 i2').
Proof.
  intros.
  split; intros ? k ?; specialize (H0 k H1).
  + rewrite Znth_sublist by lia.
    replace (k + (i2' - i1) + 0) with (k + (i2' - i1)) by lia.
    tauto.
  + rewrite Znth_sublist in H0 by lia.
    replace (k + (i2' - i1) + 0) with (k + (i2' - i1)) in H0 by lia.
    tauto.
Qed.

Lemma greatest_presuffix_fact:
  forall (str1 str2: list A) (i1 i2: Z),
    greatest_presuffix str1 str2 i1 i2 ->
    forall k,
      0 <= k <= Zlength str1 ->
      presuffix str1 str2 k i2 ->
      presuffix str1 str1 k i1.
Proof.
  intros.
  destruct H.
  pose proof H2 _ H0 H1.
  rename k into i1'.
  intros k ?.
  pose proof H (k + (i1 - i1')) ltac:(lia).
  pose proof H1 k ltac:(lia).
  replace (k + (i2 - i1')) with (k + (i1 - i1') + (i2 - i1)) in H6 by lia.
  congruence.
Qed.

Lemma presuffix_presuffix_iff:
  forall (str1 str2: list A) (i1' i1 i2: Z),
    presuffix str1 str2 i1 i2 ->
    0 <= i1' <= i1 ->
    (presuffix str1 str1 i1' i1 <->
     presuffix str1 str2 i1' i2).
Proof.
  intros.
  split; intros.
  + intros k ?.
    pose proof H (k + (i1 - i1')) ltac:(lia).
    pose proof H1 k ltac:(lia).
    replace (k + (i2 - i1')) with (k + (i1 - i1') + (i2 - i1)) by lia.
    congruence.
  + intros k ?.
    pose proof H (k + (i1 - i1')) ltac:(lia).
    pose proof H1 k ltac:(lia).
    replace (k + (i2 - i1')) with (k + (i1 - i1') + (i2 - i1)) in H4 by lia.
    congruence.
Qed.

Lemma presuffix_0:
  forall (str1 str2: list A) (i: Z),
    presuffix str1 str2 0 i.
Proof.
  intros.
  intros ? ?.
  lia.
Qed.

Lemma presuffix_add1_iff:
  forall (str1 str2: list A) (i1 i2: Z),
    0 <= i1 ->
    0 <= i2 ->
    (presuffix str1 str2 i1 (i2 + 1) <->
     i1 = 0 \/
     i1 > 0 /\
     presuffix str1 str2 (i1 - 1) i2 /\
     Znth (i1 - 1) str1 default = Znth i2 str2 default).
Proof.
  intros.
  destruct (classic (i1 = 0)).
  {
    subst.
    split; [tauto |].
    intros; apply presuffix_0.
  }
  split; intros; [right; split; [| split] |].
  + lia.
  + intros k ?.
    specialize (H2 k ltac:(lia)).
    rewrite H2.
    f_equal.
    lia.
  + specialize (H2 (i1 - 1) ltac:(lia)).
    rewrite H2.
    f_equal.
    lia.
  + destruct H2; [tauto |].
    destruct H2 as [? [? ?] ].
    unfold presuffix.
    intros.
    destruct (classic (k = i1 - 1)).
    - subst k.
      rewrite H4.
      f_equal.
      lia.
    - specialize (H3 k ltac:(lia)).
      rewrite H3.
      f_equal.
      lia.
Qed.

Lemma presuffix_ub_add1:
  forall (str1 str2: list A) (i1 i2: Z),
    0 <= i1 <= i2 ->
    presuffix_ub str1 str2 i1 i2 ->
    presuffix_ub str1 str2 (i1 + 1) (i2 + 1).
Proof.
  intros.
  intros k ? ?.
  rewrite presuffix_add1_iff in H2 by lia.
  destruct H2 as [? | [? [? ?] ] ]; [lia |].
  specialize (H0 (k - 1)).
  specialize (H0 ltac:(lia) H3).
  lia.
Qed.

Lemma presuffix_ub_add1_sublist:
  forall (str1 str2: list A) (i1 i2: Z),
    0 <= i1 <= i2 ->
    presuffix_ub (sublist 0 (Zlength str1 - 1) str1) str2 (i1 - 1) i2 ->
    presuffix_ub str1 str2 i1 (i2 + 1).
Proof.
  intros.
  intros k ? ?.
  rewrite presuffix_add1_iff in H2 by lia.
  destruct H2 as [? | [? [? ?] ] ]; [lia |].
  specialize (H0 (k - 1)).
  rewrite Zlength_sublist in H0 by lia.
  rewrite <- prefix_presuffix1 in H0 by lia.
  specialize (H0 ltac:(lia) H3).
  lia.
Qed.

Lemma greatest_presuffix_match:
  forall (str1 str2: list A) (i1 i2: Z),
    i1 >= 0 ->
    i2 >= 0 ->
    presuffix_ub str1 str2 (i1 + 1) (i2 + 1) ->
    presuffix str1 str2 i1 i2 ->
    Znth i2 str2 default = Znth i1 str1 default ->
    greatest_presuffix str1 str2 (i1 + 1) (i2 + 1).
Proof.
  intros.
  split.
  + unfold presuffix.
    intros.
    destruct (classic (k = i1)).
    - subst k.
      replace (i1 + (i2 + 1 - (i1 + 1))) with i2 by lia.
      symmetry; tauto.
    - replace (k + (i2 + 1 - (i1 + 1))) with (k + (i2 - i1)) by lia.
      apply H2; lia.
  + unfold presuffix_ub.
    intros.
    pose proof H1 k ltac:(lia) H5.
    tauto.
Qed.

Lemma greatest_presuffix_no_match:
  forall (str1 str2: list A) (i: Z),
    i >= 0 ->
    presuffix_ub str1 str2 0 (i + 1) ->
    greatest_presuffix str1 str2 0 (i + 1).
Proof.
  intros.
  split.
  + apply presuffix_0.
  + tauto.
Qed.

Lemma presuffix_ub_forward:
  forall (str1 str2: list A) (i0 i1 i2: Z),
    0 <= i0 < i1 ->
    i1 <= i2 ->
    i1 <= Zlength str1 ->
    presuffix_ub str1 str2 (i1 + 1) (i2 + 1) ->
    presuffix str1 str2 i1 i2 ->
    Znth i2 str2 default <> Znth i1 str1 default ->
    greatest_presuffix (sublist 0 (i1 - 1) str1) str1 i0 i1 ->
    presuffix_ub str1 str2 (i0 + 1) (i2 + 1) /\
    presuffix str1 str2 i0 i2.
Proof.
  intros.
  split.
  + unfold presuffix_ub.
    intros.
    pose proof H2 _ H6 H7.
    pose proof presuffix_add1_iff str1 str2 k i2 ltac:(lia) ltac:(lia).
    rewrite H9 in H7; clear H9.
    destruct H7 as [? | [? [? ?] ] ]; [lia |].
    pose proof presuffix_presuffix_iff _ _ (k - 1) _ _ H3 ltac:(lia).
    apply H11 in H9; clear H11.
    assert (k - 1 <> i1) by congruence.
    destruct H5 as [_ ?].
    pose proof prefix_presuffix1 str1 str1 (k - 1) (i1 - 1) i1 ltac:(lia).
    apply H12 in H9.
    specialize (H5 (k - 1) ltac:(rewrite Zlength_sublist; lia) H9).
    lia.
  + destruct H5 as [? _].
    pose proof prefix_presuffix1 str1 str1 i0 (i1 - 1) i1 ltac:(lia).
    pose proof presuffix_presuffix_iff str1 str2 i0 _ _ H3 ltac:(lia).
    tauto.
Qed.

Lemma presuffix_ub_fail:
  forall (str1 str2: list A) (i: Z),
    presuffix_ub str1 str2 1 (i + 1) ->
    Znth i str2 default <> Znth 0 str1 default ->
    presuffix_ub str1 str2 0 (i + 1).
Proof.
  intros.
  intros k ? ?.
  specialize (H k H1 H2).
  destruct (classic (k = 1)).
  + subst k.
    specialize (H2 0 ltac:(lia)).
    replace (0 + (i + 1 - 1)) with i in H2 by lia.
    congruence.
  + lia.
Qed.

Lemma inner_step_sound:
  forall (str_p str_t: list A) vnext i j1 j2,
    inner_step str_p vnext (Znth i str_t default) j1 j2 ->
    j1 <= i ->
    Zlength vnext = Zlength str_p + 1 ->
    in_range vnext ->
    -1 <= j1 < Zlength vnext - 1 ->
    (forall k,
       0 < k < Zlength vnext ->
       greatest_presuffix (sublist 0 (k - 1) str_p) str_p (Znth k vnext 0) k) ->
    presuffix_ub str_p str_t (j1 + 1) (i + 1) /\
    (j1 = -1 \/
     presuffix str_p str_t j1 i) ->
    presuffix_ub str_p str_t (j2 + 1) (i + 1) /\
    (j2 = -1 \/
     presuffix str_p str_t j2 i).
Proof.
  intros ? ? ? ? ? ? ?H ?H; intros.
  inversion H; subst.
  pose proof H2.(len_nonneg).
  pose proof H2.(in_range_gen) (Zlength str_p) ltac:(lia).
  pose proof H2.(in_range_gen) j1 ltac:(lia).
  destruct H5 as [? [? | ?] ]; [lia |].
  destruct (classic (j1 = 0)).
  + subst j1.
    pose proof presuffix_ub_fail _ _ _ H5 H7.
    rewrite H2.(in_range_0).
    tauto.
  + pose proof H2.(in_range_pos) j1 ltac:(lia).
    pose proof presuffix_ub_forward str_p str_t (Znth j1 vnext 0) j1 i.
    specialize (H14 ltac:(lia) ltac:(lia) ltac:(lia)).
    specialize (H4 j1 ltac:(lia)).
    specialize (H14 ltac:(tauto) ltac:(tauto) H7 H4).
    tauto.
Qed.

Lemma inner_steps_sound:
  forall (str_p str_t: list A) vnext i j1 j2,
    inner_steps str_p vnext (Znth i str_t default) j1 j2 ->
    j1 <= i ->
    Zlength vnext = Zlength str_p + 1 ->
    in_range vnext ->
    -1 <= j1 < Zlength vnext - 1 ->
    (forall k,
       0 < k < Zlength vnext ->
       greatest_presuffix (sublist 0 (k - 1) str_p) str_p (Znth k vnext 0) k) ->
    presuffix_ub str_p str_t (j1 + 1) (i + 1) /\
    (j1 = -1 \/
     presuffix str_p str_t j1 i) ->
    presuffix_ub str_p str_t (j2 + 1) (i + 1) /\
    (j2 = -1 \/
     presuffix str_p str_t j2 i).
Proof.
  intros.
  unfold inner_steps in H.
  induction_1n H.
  + tauto.
  + pose proof inner_step_j_decr _ _ _ _ _ H6 H2 ltac:(lia).
    specialize (IHrt ltac:(lia) H2 ltac:(lia) H1 H4).
    pose proof inner_step_sound _ _ _ _ _ _ H6 H0 H1 H2 H3 H4.
    tauto.
Qed.

Lemma inner_step_begin_sound_for_constr:
  forall (str_p: list A) vnext i,
    Zlength vnext <= Zlength str_p ->
    Zlength vnext = i + 1 ->
    in_range vnext ->
    (forall k,
       0 < k < Zlength vnext ->
       greatest_presuffix (sublist 0 (k - 1) str_p) str_p (Znth k vnext 0) k) ->
    presuffix_ub (sublist 0 i str_p) str_p (Znth i vnext 0 + 1) (i + 1) /\
    (Znth i vnext 0 = -1 \/
     presuffix (sublist 0 i str_p) str_p (Znth i vnext 0) i).
Proof.
  intros.
  destruct (classic (i = 0)).
  + pose proof H1.(in_range_0).
    subst i.
    split; [| tauto].
    rewrite H4.
    intros ? ? ?.
    pose proof Zlength_nonneg str_p.
    rewrite Zlength_sublist in H3 by lia.
    lia.
  + pose proof H1.(len_nonneg).
    specialize (H2 i ltac:(lia)).
    destruct H2.
    split.
    - pose proof H1.(in_range_gen) i ltac:(lia).
      apply presuffix_ub_add1_sublist.
      * lia.
      * rewrite Zlength_sublist by lia.
        rewrite Zsublist_Zsublist0 by lia.
        replace (i - 0 - 1) with (i - 1) by lia.
        replace (Znth i vnext 0 + 1 - 1) with (Znth i vnext 0) by lia.
        tauto.
    - right.
      pose proof H1.(in_range_gen) i ltac:(lia).
      pose proof prefix_presuffix1 (sublist 0 i str_p) str_p (Znth i vnext 0) (i - 1) i.
      rewrite Zsublist_Zsublist0 in H7 by lia.
      specialize (H7 ltac:(lia)).
      tauto.
Qed.

Lemma inner_step_sublist:
  forall (str_p: list A) vnext ch i j1 j2,
    j1 < i ->
    inner_step str_p vnext ch j1 j2 ->
    inner_step (sublist 0 i str_p) vnext ch j1 j2.
Proof.
  intros.
  inversion H0; subst.
  constructor; try tauto.
  rewrite Znth_sublist by lia.
  replace (j1 + 0) with j1 by lia.
  tauto.
Qed.

Lemma inner_steps_sublist:
  forall (str_p: list A) vnext ch j1 j2,
    in_range vnext ->
    -1 <= j1 < Zlength vnext - 1 ->
    inner_steps str_p vnext ch j1 j2 ->
    inner_steps (sublist 0 (Zlength vnext - 1) str_p) vnext ch j1 j2.
Proof.
  intros.
  induction_1n H1.
  + reflexivity.
  + pose proof inner_step_j_decr _ _ _ _ _ H2 H.
    pose proof inner_step_sublist _ _ _ (Zlength vnext - 1) j1 j0 ltac:(lia) H2.
    transitivity_1n j0.
    - tauto.
    - apply IHrt.
      * tauto.
      * lia.
Qed.

Lemma inner_steps_sound_for_constr:
  forall (str_p: list A) vnext i j1 j2,
    inner_steps str_p vnext (Znth i str_p default) j1 j2 ->
    Zlength vnext <= Zlength str_p ->
    in_range vnext ->
    Zlength vnext = i + 1 ->
    j1 = Znth i vnext 0 ->
    (forall k,
       0 < k < Zlength vnext ->
       greatest_presuffix (sublist 0 (k - 1) str_p) str_p (Znth k vnext 0) k) ->
    presuffix_ub (sublist 0 i str_p) str_p (j1 + 1) (i + 1) /\
    (j1 = -1 \/
     presuffix (sublist 0 i str_p) str_p j1 i) ->
    presuffix_ub (sublist 0 i str_p) str_p (j2 + 1) (i + 1) /\
    (j2 = -1 \/
     presuffix (sublist 0 i str_p) str_p j2 i).
Proof.
  intros.
  pose proof H1.(len_nonneg).
  pose proof H1.(in_range_gen) i ltac:(lia).
  pose proof inner_steps_sublist _ _ (Znth i str_p default) j1 j2 H1 ltac:(lia) H.
  pose proof inner_steps_sound _ _ _ _ _ _ H8.
  rewrite Zlength_sublist in H9 by lia.
  specialize (H9 ltac:(lia) ltac:(lia) H1 ltac:(lia)).
  rewrite H2 in H9.
  replace (i + 1 - 1) with i in H9 by lia.
  revert H5; apply H9; clear H9.
  intros.
  specialize (H4 k ltac:(lia)).
  rewrite Zsublist_Zsublist0 by lia.
  destruct H4.
  split.
  + apply prefix_presuffix2.
    - pose proof H1.(in_range_gen) k ltac:(lia).
      lia.
    - tauto.
  + intros k' ? ?.
    apply (H9 k' H10).
    apply prefix_presuffix2 in H11.
    - tauto.
    - rewrite Zlength_sublist in H10 by lia.
      lia.
Qed.

Lemma constr_step_sound:
  forall (str_p: list A) vnext vnext',
    constr_step str_p vnext vnext' ->
    Zlength vnext <= Zlength str_p ->
    in_range vnext ->
    (forall k,
       0 < k < Zlength vnext ->
       greatest_presuffix (sublist 0 (k - 1) str_p) str_p (Znth k vnext 0) k) ->
    (forall k,
       0 < k < Zlength vnext' ->
       greatest_presuffix (sublist 0 (k - 1) str_p) str_p (Znth k vnext' 0) k).
Proof.
  intros.
  inversion H; subst.
  + destruct (classic (k < Zlength vnext)).
    - specialize (H2 k ltac:(lia)).
      pose proof H1.(len_nonneg).
      rewrite app_Znth1 by lia.
      tauto.
    - assert (k = Zlength vnext). {
        rewrite Zlength_app in H3.
        change (Zlength [j + 1]) with 1 in H3.
        lia.
      }
      subst k; clear H3 H8.
      rewrite app_Znth2 by lia.
      replace (Zlength vnext - Zlength vnext) with 0 by lia.
      change (Znth 0 [j + 1] 0) with (j + 1).
      rewrite <- H5.
      replace (i + 1 - 1) with i by lia.
      pose proof H1.(len_nonneg).
      pose proof H1.(in_range_gen) i ltac:(lia).
      pose proof inner_steps_sound_for_constr _ _ _ _ _ H6 H0 H1 ltac:(lia) ltac:(lia) H2.
      pose proof inner_step_begin_sound_for_constr _ _ i H0 ltac:(lia) H1 H2.
      apply H9 in H10; clear H9.
      pose proof inner_steps_j_decr _ _ _ _ _ H6 H1 ltac:(lia).
      destruct H10 as [? [? | ?] ]; [lia |].
      apply greatest_presuffix_match.
      * lia.
      * lia.
      * tauto.
      * tauto.
      * rewrite Znth_sublist by lia.
        replace (j + 0) with j by lia.
        tauto.
  + destruct (classic (k < Zlength vnext)).
    - specialize (H2 k ltac:(lia)).
      pose proof H1.(len_nonneg).
      rewrite app_Znth1 by lia.
      tauto.
    - assert (k = Zlength vnext). {
        rewrite Zlength_app in H3.
        change (Zlength [0]) with 1 in H3.
        lia.
      }
      subst k; clear H3 H6.
      rewrite app_Znth2 by lia.
      replace (Zlength vnext - Zlength vnext) with 0 by lia.
      change (Znth 0 [0] 0) with (0).
      rewrite <- H4.
      replace (i + 1 - 1) with i by lia.
      pose proof H1.(len_nonneg).
      pose proof H1.(in_range_gen) i ltac:(lia).
      pose proof inner_steps_sound_for_constr _ _ _ _ _ H5 H0 H1 ltac:(lia) ltac:(lia) H2.
      pose proof inner_step_begin_sound_for_constr _ _ i H0 ltac:(lia) H1 H2.
      apply H7 in H8; clear H7.
      apply greatest_presuffix_no_match.
      * lia.
      * replace (-1 + 1) with 0 in H8 by lia.
        tauto.
Qed.

Lemma clos_refl_trans_constr_step_sound:
  forall (str_p: list A) vnext vnext',
    clos_refl_trans (constr_step str_p) vnext vnext' ->
    Zlength vnext' <= Zlength str_p + 1 ->
    in_range vnext ->
    (forall k,
       0 < k < Zlength vnext ->
       greatest_presuffix (sublist 0 (k - 1) str_p) str_p (Znth k vnext 0) k) ->
    (forall k,
       0 < k < Zlength vnext' ->
       greatest_presuffix (sublist 0 (k - 1) str_p) str_p (Znth k vnext' 0) k).
Proof.
  intros until vnext'. intros ? ? ? ?.
  induction_1n H.
  + revert k H.
    tauto.
  + revert k H3.
    pose proof constr_step_in_range _ _ _ H4 H1.
    specialize (IHrt ltac:(tauto) ltac:(lia)).
    pose proof constr_step_sound _ _ _ H4.
    pose proof clos_refl_trans_constr_step_in_range _ _ _ H ltac:(tauto).
    specialize (H5 ltac:(lia) ltac:(tauto) ltac:(tauto)).
    tauto.
Qed.

Lemma inner_step_begin_sound_for_match:
  forall (str_p str_t: list A) i j,
    greatest_presuffix str_p str_t j i ->
    0 <= j <= i ->
    presuffix_ub str_p str_t (j + 1) (i + 1) /\
    (j = -1 \/ presuffix str_p str_t j i).
Proof.
  intros.
  destruct H.
  split.
  + apply presuffix_ub_add1; tauto.
  + tauto.
Qed.

Lemma match_step_sound:
  forall (str_p str_t: list A) vnext i j i' j',
    match_step str_p str_t vnext (i, j) (i', j') ->
    Zlength vnext = Zlength str_p + 1 /\ in_range vnext ->
    0 <= j <= i ->
    (forall k,
       0 < k < Zlength vnext ->
       greatest_presuffix (sublist 0 (k - 1) str_p) str_p (Znth k vnext 0) k) ->
    greatest_presuffix str_p str_t j i ->
    greatest_presuffix str_p str_t j' i'.
Proof.
  intros.
  inversion H; subst.
  + pose proof inner_steps_sound _ _ _ i _ _ H10 ltac:(lia) ltac:(lia)
               ltac:(tauto) ltac:(lia) H2.
    pose proof inner_steps_j_decr _ _ _ _ _ H10 ltac:(tauto) ltac:(lia).
    pose proof inner_step_begin_sound_for_match str_p str_t i j ltac:(tauto) ltac:(tauto).
    apply H4 in H6; clear H4.
    destruct H6 as [? [? | ?] ]; [lia |].
    apply greatest_presuffix_match.
    - lia.
    - lia.
    - tauto.
    - tauto.
    - tauto.
  + pose proof inner_steps_sound _ _ _ i _ _ H9 ltac:(lia) ltac:(lia)
               ltac:(tauto) ltac:(lia) H2.
    pose proof inner_steps_j_decr _ _ _ _ _ H9 ltac:(tauto) ltac:(lia).
    pose proof inner_step_begin_sound_for_match str_p str_t i j ltac:(tauto) ltac:(tauto).
    apply H4 in H6; clear H4.
    destruct H6 as [? _].
    apply greatest_presuffix_no_match.
    - lia.
    - apply H4.
Qed.

End KMP.